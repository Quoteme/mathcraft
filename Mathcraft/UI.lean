import «Mathcraft».Basic

namespace Mathcraft

namespace UI

def listWorlds : IO Unit := do
  IO.println s!"Installed Mathcraft worlds:"
  let worlds ← Mathcraft.WorldLoader.listWorlds
  for world in worlds do
    IO.println s!"· {repr world}"
  if worlds.isEmpty then
    IO.println "‼️ No worlds found!"

end UI

end Mathcraft
