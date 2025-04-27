variable { α β γ : Type }

class Coder where
  encode: (x: α) → β
  decode: (y: β) → Option α
  loseless : ∀ (a: α), decode (encode a) = a

def ChainCoder (c₁: @Coder α β) (c₂: @Coder β γ) : @Coder α γ := {
  encode := fun x => c₂.encode (c₁.encode x)

  decode := fun z => match (c₂.decode z) with
  | none => none
  | some y => c₁.decode y

  loseless := by
    intro x
    rw [c₂.loseless]
    simp
    rw [c₁.loseless]
}
