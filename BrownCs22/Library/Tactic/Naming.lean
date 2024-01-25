import Lean

def isValidHypName (nm : String) : Bool :=
  nm.startsWith "ih" ||
  match nm.get? 0 with
    | some c => c == 'h'
    | _ => false

def isValidDataName (nm : String) : Bool :=
  nm.get? 0 != some 'h'
