(l |-> 1 , m |-> True, <>).l

-- Accepted!
--    ⋅ ⊩ l ↦ 1, (m ↦ True, ⟨⟩).l ⇒a End
-- -->{ Rule: ⇒Proj           }
--    ⋅ ⊩ l ↦ 1, (m ↦ True, ⟨⟩) ⇒b b ▹c,a0 c → a0 ⊗ (LABEL l) ➤a End
-- -->{ Rule: ⇒⟨⟩Cons         }
--    ⋅ ⊩ 1 ⇒b0 m ↦ True, ⟨⟩ ⇒c0 ((LABEL l) → b0) ∩ c0 ▹c,a0 c → a0 ⊗ (LABEL l) ➤a End
-- -->{ Rule: ⇒Int            }
--    ⋅ ⊩ m ↦ True, ⟨⟩ ⇒c0 ((LABEL l) → Int) ∩ c0 ▹c,a0 c → a0 ⊗ (LABEL l) ➤a End
-- -->{ Rule: ⇒⟨⟩Cons         }
--    ⋅ ⊩ True ⇒b ⟨⟩ ⇒b0 ((LABEL l) → Int) ∩ (((LABEL m) → b) ∩ b0) ▹c,a0 c → a0 ⊗ (LABEL l) ➤a End
-- -->{ Rule: ⇒Bool           }
--    ⋅ ⊩ ⟨⟩ ⇒b0 ((LABEL l) → Int) ∩ (((LABEL m) → Bool) ∩ b0) ▹c,a0 c → a0 ⊗ (LABEL l) ➤a End
-- -->{ Rule: ⇒⟨⟩             }
--    ⋅ ⊩ ((LABEL l) → Int) ∩ (((LABEL m) → Bool) ∩ Unit) ▹c,a0 c → a0 ⊗ (LABEL l) ➤a End
-- -->{ Rule: ▹∩1             }
--    ⋅ ⊩ (LABEL l) → Int ▹c,a0 c → a0 ⊗ (LABEL l) ➤a End
-- -->{ Rule: ▹→              }
--    ⋅ ⊩ (LABEL l) → Int ⊗ (LABEL l) ➤a End
-- -->{ Rule: ⊗➤              }
--    ⋅ ⊩ End ⊩ (LABEL l) ≤ (LABEL l)
-- -->{ Rule: ≤Label          }
--    ⋅ ⊩ End
-- -->{ Rule: Dummy           }