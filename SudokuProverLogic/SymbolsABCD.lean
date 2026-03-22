import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

set_option linter.style.whitespace false


inductive SymbolsABCD
| A
| B
| C
| D
deriving Repr, BEq, DecidableEq

def Symbols4.toStr : SymbolsABCD → String
  | .A => "A"
  | .B => "B"
  | .C => "C"
  | .D => "D"

-- make these defitions accessible in python
def A := SymbolsABCD.A
def B := SymbolsABCD.B
def C := SymbolsABCD.C
def D := SymbolsABCD.D

-- instance: ToString SymbolsABCD where
--   toString := SymbolsABCD.toStr

instance : Fintype SymbolsABCD where
  elems := {SymbolsABCD.A, .B, .C, .D}
  complete x := by cases x <;> simp

@[simp]
lemma card_SymbolsABCD: Fintype.card SymbolsABCD = 4 := by
  simp [Fintype.card, Finset.univ, Fintype.elems]

def SymbolsABCD.ofStr : String → SymbolsABCD
  | "A" => .A
  | "B" => .B
  | "C" => .C
  | "D" => .D
  | _   => .A

instance : Coe String SymbolsABCD where
  coe := SymbolsABCD.ofStr

@[simp] theorem symbols_A_eq : SymbolsABCD.A = ("A" : SymbolsABCD) := rfl
@[simp] theorem symbols_B_eq : SymbolsABCD.B = ("B" : SymbolsABCD) := rfl
@[simp] theorem symbols_C_eq : SymbolsABCD.C = ("C" : SymbolsABCD) := rfl
@[simp] theorem symbols_D_eq : SymbolsABCD.D = ("D" : SymbolsABCD) := rfl
