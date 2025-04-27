variable { α β γ : Type }

class Coder where
  encode: (x: α) → β
  decode: (y: β) → Option α

class Loseless ( c: @Coder α β ) where
  loseless : ∀ (a: α), c.decode (c.encode a) = a

def ChainCoder (c₁: @Coder α β) (c₂: @Coder β γ) [Loseless c₁] [Loseless c₂] : @Coder α γ := {
  encode := fun x => c₂.encode (c₁.encode x)
  decode := fun z => match (c₂.decode z) with
  | none => none
  | some y => c₁.decode y
}

instance (c₁: @Coder α β) (c₂: @Coder β γ) [h₁: Loseless c₁] [h₂: Loseless c₂]:
  @Loseless α γ (ChainCoder c₁ c₂) where
  loseless := by
    intro x
    simp [Coder.encode, Coder.decode, ChainCoder]
    rw [h₂.loseless]
    simp
    rw [h₁.loseless]
