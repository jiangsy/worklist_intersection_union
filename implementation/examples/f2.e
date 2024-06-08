-- function f2(o: { m: number, n: boolean }): number { return o.m }

let f :: ((Label m -> Int) /\ (Label n -> Bool)) -> Int = \x -> x.m in f

-- Accepted!
--    ⋅ ⊩ let f :: ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int = λx. (x.m) in f ⇒a End
-- -->{ Rule: ⇒LetA           }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int ⊩ λx. (x.m) ⇐ ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int ⊩ f ⇒a End
-- -->{ Rule: ⇒Var            }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int ⊩ λx. (x.m) ⇐ ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int ⊩ End
-- -->{ Rule: Dummy           }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int ⊩ λx. (x.m) ⇐ ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int
-- -->{ Rule: ⇐λ              }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ y.m ⇐ Int
-- -->{ Rule: ⇐Sub            }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ y.m ⇒a a ≤ Int
-- -->{ Rule: ⇒Proj           }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ y ⇒b b ▹c,a0 c → a0 ⊗ (LABEL m) ➤a a ≤ Int
-- -->{ Rule: ⇒Var            }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ▹c,a0 c → a0 ⊗ (LABEL m) ➤a a ≤ Int
-- -->{ Rule: ▹∩1             }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ (LABEL m) → Int ▹c,a0 c → a0 ⊗ (LABEL m) ➤a a ≤ Int
-- -->{ Rule: ▹→              }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ (LABEL m) → Int ⊗ (LABEL m) ➤a a ≤ Int
-- -->{ Rule: ⊗➤              }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ Int ≤ Int ⊩ (LABEL m) ≤ (LABEL m)
-- -->{ Rule: ≤Label          }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ Int ≤ Int
-- -->{ Rule: ≤Int            }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool)
-- -->{ Rule: GCVar           }
--    ⋅, f : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int
-- -->{ Rule: GCVar           }