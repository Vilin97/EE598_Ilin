def getLines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines := #[]
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do
    lines := lines.push (currLine.dropEnd 1).toString
    currLine ← stdin.getLine
  return lines

def upperCaseLines : IO Unit := do
  let lines ← getLines
  for line in lines do
    IO.println line.toUpper

def main : IO Unit :=
  upperCaseLines
