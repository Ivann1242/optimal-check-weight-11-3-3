import LowWeight.Transform
import LowWeight.Spec

/-! Bit-matrix view of a generator family, and single-qubit errors. -/

namespace LowWeight

variable {m n : ℕ}

/-- X-bits of the generators. -/
def toX (g : Fin m → Pauli n) : Fin m → Fin n → Bool := fun i j => decide ((g i j).1 = 1)

/-- Z-bits of the generators. -/
def toZ (g : Fin m → Pauli n) : Fin m → Fin n → Bool := fun i j => decide ((g i j).2 = 1)

/-- Syndrome column of the error of type `t` on qubit `j` for the family `g`. -/
def synP (g : Fin m → Pauli n) (j : Fin n) (t : Fin 3) : Fin m → Bool := syn (toX g) (toZ g) j t

/-- The single-qubit Pauli of type `t` (0: Z, 1: X, 2: Y), as an element of `F × F`. -/
def pauliOf (t : Fin 3) : F × F := if t = 0 then (0, 1) else if t = 1 then (1, 0) else (1, 1)

/-- The single-qubit error of type `t` on qubit `j`. -/
def err (j : Fin n) (t : Fin 3) : Pauli n := Pi.single j (pauliOf t)

end LowWeight
