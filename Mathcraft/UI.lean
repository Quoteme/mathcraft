import «Mathcraft».Library
import Init.Data.List.Basic

namespace Mathcraft

namespace UI

namespace Text

abbrev Paragraph := List String

def String.lines (s : String) : Paragraph :=
  s.splitOn "\n"

def String.repeat (s : String) (n : Nat) : String :=
  String.join (List.replicate n s)

def Paragraph.join (p : Paragraph) : String :=
  String.intercalate "\n" p

def Paragraph.width (p : Paragraph) : Nat :=
  p.foldl (init := 0) (λ w line => Nat.max w line.length)

/--
Put a box around an arbitrary number of lines of text.
-/
def Paragraph.box (paragraph : Paragraph) : String :=
  let width := paragraph.width
  let top := "┌" ++ String.repeat "─" (width + 2) ++ "┐"
  let bottom := "└" ++ String.repeat "─" (width + 2) ++ "┘"
  let middle := paragraph.map (λ line => "│ " ++ line ++ String.repeat " " (width - line.length) ++ " │")
  let lines := (top :: middle) ++ [bottom]
  String.intercalate "\n" lines

structure Table where
  header : List String
  rows : List (List String)
deriving Repr

/--
Writing the table as a matrix ( String )ⁿˣᵐ, find the width, ie. `n`
-/
def Table.width (t : Table) : Nat :=
  let headerWidth := t.header.length
  let rowWidth := t.rows.foldl (init := 0) (λ w row => Nat.max w row.length)
  Nat.max headerWidth rowWidth

/--
Writing the table as a matrix ( String )ⁿˣᵐ, find the height, ie. `m`
-/
def Table.height (t : Table) : Nat :=
  t.rows.length

/--
Because rows is a list of list, which might have different numbers of lengths, we fill each list until they are all the same length
-/
def Table.fill (t : Table) : Table := {
  header := t.header ++ List.replicate (t.width - t.header.length) ""
  rows := t.rows.map (λ r ↦ r ++ List.replicate (t.width - r.length) "")
}

/--
Find the width of the `i`th column
-/
def Table.columnWidth (t : Table) (i : Nat) : Nat :=
  (t.header ++ t.rows.map (λ row => row.get! i)).foldl (init := 0) (λ w col => Nat.max w col.length)

/--
The strings in each column might be of different lengths. Using this function, we normalize the length of each column
-/
def Table.fillString (t : Table) : Table :=
  let filled := t.fill
  let columnWidths := filled.header.enum.map (λ (i,_) ↦ t.columnWidth i)
  let filledRows := filled.rows.map (λ row ↦ row.enum.map (λ (i, cell) ↦ cell ++ String.repeat " " (columnWidths.get! i - cell.length)))
  let filledHeader := filled.header.enum.map (λ (i, cell) ↦ cell ++ String.repeat " " (columnWidths.get! i - cell.length))
  { filled with rows := filledRows, header := filledHeader }

#check List.getLastD

/--
A single line that seperates different rows in a table
-/
def Table.seperatorLine (row : List String) (beginning lineator crossing ending : String) : String :=
  -- "┌"
  beginning ++
  -- "─...─|─...─|─...─|"
  String.join (row.dropLast.map (λ cell => String.repeat lineator cell.length ++ crossing)) ++
  -- "─..."
  String.repeat lineator (row.getLastD "").length ++
  -- "┐"
  ending


def Table.box (t : Table) : String :=
  let filled := t.fillString
  let columnWidths := filled.header.enum.map (λ (i,_) ↦ t.columnWidth i)
  let headerTop := Table.seperatorLine filled.header "┌─" "─" "─┬─" "─┐"
  let headerBottom := Table.seperatorLine filled.header "├─" "─" "─┼─" "─┤"
  let headerMiddle := "│ " ++ String.intercalate " │ " (filled.header.enum.map (λ (i, cell) ↦ cell ++ String.repeat " " (columnWidths.get! i - cell.length))) ++ " │"
  let rowMiddle (row : List String) : String :=
    "│ " ++ String.intercalate " │ " (row.enum.map (λ (i, cell) ↦ cell ++ String.repeat " " (columnWidths.get! i - cell.length))) ++ " │"
  let rowBottom := Table.seperatorLine filled.header "└─" "─" "─┴─" "─┘"
  String.intercalate "\n" $ [headerTop, headerMiddle, headerBottom] ++ filled.rows.map rowMiddle ++ [rowBottom]

-- #eval IO.println $ Table.mk ( header := ["Name", "Age", "", "Test!!!"] ) ( rows := [["Alice", "20"], ["Bob", "30"], ["Charlie", "40"]] ).box

end Text

namespace StartMenu

def listWorlds : IO Unit := do
  IO.println s!"Installed Mathcraft worlds:"
  let worlds ← Library.listWorlds
  -- for world in worlds do
  --   IO.println s!"· {repr world}"
  let table : Text.Table := {
    header := ["Directory"]
    rows := worlds.map (λ world ↦ [world.directory.toString])
  }
  IO.println table.box
  if worlds.isEmpty then
    IO.println "No worlds saved..."

def loadWorld : IO World := do
  IO.println "Loading a Mathcraft world..."
  let worlds ← Library.listWorlds
  IO.println $ Text.Paragraph.box ["Enter the number of the world you want to load."]
  IO.println $ Text.Table.box {
    header := ["Number", "Directory"]
    rows := worlds.enum.map (λ (i, world) ↦ [s!"{i}", world.directory.toString])
  }
  IO.println "Number:"
  let number := ( ← (← IO.getStdin).getLine ).toNat!
  let world := worlds.get! number
  return world

def newWorld : IO Unit := do
  IO.println "Creating a new Mathcraft world..."
  IO.println "Name:"
  let name := ( ← (← IO.getStdin).getLine ).trim
  let world ← Library.newWorld name
  IO.println s!"✅ Created world {repr world}"

unsafe def loop : IO Unit := do
  IO.println "What do you want to do?"
  let prompt : Text.Table := {
    header := ["Command", "Description"]
    rows := [
      ["list", "List installed Mathcraft worlds"],
      ["load", "Load an existing Mathcraft world"],
      ["new", "Create a new Mathcraft world"],
      ["exit", "Exit the Mathcraft start menu"]
    ]
  }
  IO.println prompt.box
  let cmd ← (← IO.getStdin).getLine <&> String.trim
  match cmd with
  | "list" => listWorlds; loop
  | "load" => IO.println "Not implemented"; loop
  | "new" => newWorld; loop
  | "exit" => pure ()
  | _ => IO.println "❌ Unknown command"; loop

unsafe def main : IO Unit := do
  let greeting : Text.Paragraph := ["Welcome to Mathcraft!"]
  IO.println greeting.box
  loop

end StartMenu

end UI

end Mathcraft
