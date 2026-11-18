$pdf_mode = 5; # xelatex -> pdf, instead of pdflatex
$postscript_mode = $dvi_mode = 0;

# Without an explicit target, latexmk defaults to building every .tex file
# in the directory. This project splits into many \input-ed chapter files
# (sections/*.tex) that aren't standalone
# documents, so that default tries (and fails) to compile each of them.
# Pin the default target to the actual root document.
@default_files = ('mathcraft.tex');

# minted (see imports.tex) shells out to the `latexminted` helper bundled
# with TeX Live, which as of latexminted 0.6.0 / minted 3.7.0 crashes under
# Python >= 3.14 (argparse now always passes a `color` kwarg to subparsers,
# which latexminted's ArgParser subclass does not accept). tools/pythonpath/
# contains a sitecustomize.py that patches around this; put it on PYTHONPATH
# for every xelatex invocation. Safe/no-op once the upstream bug is fixed.
use File::Basename;
use Cwd 'abs_path';
my $latexmkrc_dir = dirname(abs_path(__FILE__));
$ENV{'PYTHONPATH'} = "$latexmkrc_dir/tools/pythonpath" . ($ENV{'PYTHONPATH'} ? ":$ENV{'PYTHONPATH'}" : '');

$xelatex = 'xelatex -shell-escape -synctex=1 -interaction=nonstopmode -file-line-error %O %S'; # -shell-escape required by minted
