-- function f2(o: { m: number, n: boolean }): number { return o.m }

(\x -> x.m) :: ((Label m -> Int) /\ (Label n -> Bool)) -> Int

-- Accepted!
--    ⋅ ⊩ λx. (x.m) :: ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int ⇒a End
-- -->{ Rule: ⇒Anno           }
--    ⋅ ⊩ End ⊩ λx. (x.m) ⇐ ((LABEL m) → Int) ∩ ((LABEL n) → Bool) → Int
-- -->{ Rule: ⇐λ              }
--    ⋅ ⊩ End, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ y.m ⇐ Int
-- -->{ Rule: ⇐Sub            }
--    ⋅ ⊩ End, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ y.m ⇒a a ≤ Int
-- -->{ Rule: ⇒Proj           }
--    ⋅ ⊩ End, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ y ⇒b b ▹c,a0 c → a0 ⊗ (LABEL m) ➤a a ≤ Int
-- -->{ Rule: ⇒Var            }
--    ⋅ ⊩ End, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ▹c,a0 c → a0 ⊗ (LABEL m) ➤a a ≤ Int
-- -->{ Rule: ▹∩1             }
--    ⋅ ⊩ End, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ (LABEL m) → Int ▹c,a0 c → a0 ⊗ (LABEL m) ➤a a ≤ Int
-- -->{ Rule: ▹→              }
--    ⋅ ⊩ End, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ (LABEL m) → Int ⊗ (LABEL m) ➤a a ≤ Int
-- -->{ Rule: ⊗➤              }
--    ⋅ ⊩ End, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ Int ≤ Int ⊩ (LABEL m) ≤ (LABEL m)
-- -->{ Rule: ≤Label          }
--    ⋅ ⊩ End, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool) ⊩ Int ≤ Int
-- -->{ Rule: ≤Int            }
--    ⋅ ⊩ End, y : ((LABEL m) → Int) ∩ ((LABEL n) → Bool)
-- -->{ Rule: GCVar           }
--    ⋅ ⊩ End
-- -->{ Rule: Dummy           }