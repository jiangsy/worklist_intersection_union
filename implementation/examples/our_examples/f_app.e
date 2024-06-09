(\x -> x) 1

-- Accepted!
--    ⋅ ⊩ (λx. x) 1 ⇒a End
-- -->{ Rule: ⇒App            }
--    ⋅ ⊩ λx. x ⇒b b ▹c,a0 c → a0 ⊙ 1 ➤a End
-- -->{ Rule: ⇒→Mono          }
--    ⋅, b0 : ⬒, c0 : ⬒ ⊩ b0 → c0 ▹c,a0 c → a0 ⊙ 1 ➤a End, y : b0 ⊩ y ⇐ c0
-- -->{ Rule: ⇐Sub            }
--    ⋅, b0 : ⬒, c0 : ⬒ ⊩ b0 → c0 ▹c,a0 c → a0 ⊙ 1 ➤a End, y : b0 ⊩ y ⇒b b ≤ c0
-- -->{ Rule: ⇒Var            }
--    ⋅, b0 : ⬒, c0 : ⬒ ⊩ b0 → c0 ▹c,a0 c → a0 ⊙ 1 ➤a End, y : b0 ⊩ b0 ≤ c0
-- -->{ Rule: ≤MonoL          }
--    ⋅, c0 : ⬒ ⊩ c0 → c0 ▹c,a0 c → a0 ⊙ 1 ➤a End, y : c0
-- -->{ Rule: GCVar           }
--    ⋅, c0 : ⬒ ⊩ c0 → c0 ▹c,a0 c → a0 ⊙ 1 ➤a End
-- -->{ Rule: ▹→              }
--    ⋅, c0 : ⬒ ⊩ c0 → c0 ⊙ 1 ➤a End
-- -->{ Rule: ⊙➤              }
--    ⋅, c0 : ⬒ ⊩ End ⊩ 1 ⇐ c0
-- -->{ Rule: ⇐Sub            }
--    ⋅, c0 : ⬒ ⊩ End ⊩ 1 ⇒a a ≤ c0
-- -->{ Rule: ⇒Int            }
--    ⋅, c0 : ⬒ ⊩ End ⊩ Int ≤ c0
-- -->{ Rule: ≤MonoR          }
--    ⋅ ⊩ End
-- -->{ Rule: Dummy           }