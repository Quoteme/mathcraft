"""
Workaround for a crash in the `latexminted` helper (used by the `minted`
LaTeX package, see imports.tex) under Python >= 3.14.

Python 3.14 added colorized --help output to argparse. As part of that,
argparse.ArgumentParser's subparsers action now always forwards a `color`
keyword argument to every subparser it creates:
    https://docs.python.org/3/whatsnew/3.14.html (argparse)
`latexminted` (as of its 0.6.0 release, bundled with TeX Live 2025's minted
package) defines its own ArgParser(argparse.ArgumentParser) subclass whose
__init__ only accepts `prog`, so it does not expect this new `color` keyword
and crashes with:
    TypeError: ArgParser.__init__() got an unexpected keyword argument 'color'

This directory is added to PYTHONPATH (see .latexmkrc) purely so this module
gets auto-imported by Python's `site` module on startup. It patches
argparse._SubParsersAction.add_parser to drop an unrecognized `color` kwarg
and retry, which is enough for latexminted to work again. It is a no-op (via
the try/except) once latexminted or Python fixes this upstream, so it is safe
to leave in place; feel free to delete this file plus the PYTHONPATH line in
.latexmkrc once that happens.
"""
import argparse
import inspect

# The buggy line, inside argparse._SubParsersAction.add_parser itself, is:
#     if kwargs.get('color') is None:
#         kwargs['color'] = self._color
#     ...
#     parser = self._parser_class(**kwargs)
# i.e. `color` is injected *inside* the original method, so wrapping it and
# stripping `color` from the *caller*-supplied kwargs does not help. Replace
# the method outright with a copy that only injects `color` when the target
# parser class actually declares that parameter.


def _add_parser(self, name, *, deprecated=False, **kwargs):
    if kwargs.get("prog") is None:
        kwargs["prog"] = "%s %s" % (self._prog_prefix, name)

    if kwargs.get("color") is None:
        try:
            accepts_color = "color" in inspect.signature(self._parser_class).parameters
        except (TypeError, ValueError):
            accepts_color = False
        if accepts_color:
            kwargs["color"] = self._color
        else:
            kwargs.pop("color", None)

    aliases = kwargs.pop("aliases", ())

    if name in self._name_parser_map:
        raise ValueError(f"conflicting subparser: {name}")
    for alias in aliases:
        if alias in self._name_parser_map:
            raise ValueError(f"conflicting subparser alias: {alias}")

    if "help" in kwargs:
        help = kwargs.pop("help")
        choice_action = self._ChoicesPseudoAction(name, aliases, help)
        self._choices_actions.append(choice_action)
    else:
        choice_action = None

    parser = self._parser_class(**kwargs)
    if choice_action is not None:
        parser._check_help(choice_action)
    self._name_parser_map[name] = parser

    for alias in aliases:
        self._name_parser_map[alias] = parser

    if deprecated:
        self._deprecated.add(name)
        self._deprecated.update(aliases)

    return parser


argparse._SubParsersAction.add_parser = _add_parser
