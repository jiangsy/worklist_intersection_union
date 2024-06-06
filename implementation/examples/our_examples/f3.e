/\ a. ((\x -> x x) :: ((a /\ (a -> a)) -> a))

Accepted!
   ⋅ ⊩ let f :: ∀a. a ∩ (a → a) → a = Λa. (λx. x x :: a ∩ (a → a) → a) in f ⇒b End
-->{ Rule: ⇒LetA           }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ Λa. (λx. x x :: a ∩ (a → a) → a) ⇐ ∀a. a ∩ (a → a) → a ⊩ f ⇒b End
-->{ Rule: ⇒Var            }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ Λa. (λx. x x :: a ∩ (a → a) → a) ⇐ ∀a. a ∩ (a → a) → a ⊩ End
-->{ Rule: Dummy           }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ Λa. (λx. x x :: a ∩ (a → a) → a) ⇐ ∀a. a ∩ (a → a) → a
-->{ Rule: ⇐Sub            }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ Λa. (λx. x x :: a ∩ (a → a) → a) ⇒b b ≤ ∀a. a ∩ (a → a) → a
-->{ Rule: ⇒ΛAnno          }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □ ⊩ λx. x x ⇐ c ∩ (c → c) → c
-->{ Rule: ⇐λ              }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ y y ⇐ c
-->{ Rule: ⇐Sub            }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ y y ⇒b b ≤ c
-->{ Rule: ⇒App            }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ y ⇒a0 a0 ▹b0,c0 b0 → c0 ⊙ y ➤b b ≤ c
-->{ Rule: ⇒Var            }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ c ∩ (c → c) ▹b0,c0 b0 → c0 ⊙ y ➤b b ≤ c
-->{ Rule: ▹∩2             }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ c → c ▹b0,c0 b0 → c0 ⊙ y ➤b b ≤ c
-->{ Rule: ▹→              }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ c → c ⊙ y ➤b b ≤ c
-->{ Rule: ⊙➤              }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ c ≤ c ⊩ y ⇐ c
-->{ Rule: ⇐Sub            }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ c ≤ c ⊩ y ⇒b b ≤ c
-->{ Rule: ⇒Var            }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ c ≤ c ⊩ c ∩ (c → c) ≤ c
-->{ Rule: ≤∩L1            }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ c ≤ c ⊩ c ≤ c
-->{ Rule: ≤TVar           }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c) ⊩ c ≤ c
-->{ Rule: ≤TVar           }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □, y : c ∩ (c → c)
-->{ Rule: GCVar           }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a, c : □
-->{ Rule: GCTVar          }
   ⋅, f : ∀a. a ∩ (a → a) → a ⊩ ∀c. c ∩ (c → c) → c ≤ ∀a. a ∩ (a → a) → a
-->{ Rule: ≤∀              }
   ⋅, f : ∀a. a ∩ (a → a) → a, b : ■ ⊩ b ∩ (b → b) → b ≤ b ∩ (b → b) → b
-->{ Rule: ≤→              }
   ⋅, f : ∀a. a ∩ (a → a) → a, b : ■ ⊩ b ∩ (b → b) ≤ b ∩ (b → b) ⊩ b ≤ b
-->{ Rule: ≤TVar           }
   ⋅, f : ∀a. a ∩ (a → a) → a, b : ■ ⊩ b ∩ (b → b) ≤ b ∩ (b → b)
-->{ Rule: ≤∩R             }
   ⋅, f : ∀a. a ∩ (a → a) → a, b : ■ ⊩ b ∩ (b → b) ≤ b ⊩ b ∩ (b → b) ≤ b → b
-->{ Rule: ≤∩L2            }
   ⋅, f : ∀a. a ∩ (a → a) → a, b : ■ ⊩ b ∩ (b → b) ≤ b ⊩ b → b ≤ b → b
-->{ Rule: ≤→              }
   ⋅, f : ∀a. a ∩ (a → a) → a, b : ■ ⊩ b ∩ (b → b) ≤ b ⊩ b ≤ b ⊩ b ≤ b
-->{ Rule: ≤TVar           }
   ⋅, f : ∀a. a ∩ (a → a) → a, b : ■ ⊩ b ∩ (b → b) ≤ b ⊩ b ≤ b
-->{ Rule: ≤TVar           }
   ⋅, f : ∀a. a ∩ (a → a) → a, b : ■ ⊩ b ∩ (b → b) ≤ b
-->{ Rule: ≤∩L1            }
   ⋅, f : ∀a. a ∩ (a → a) → a, b : ■ ⊩ b ≤ b
-->{ Rule: ≤TVar           }
   ⋅, f : ∀a. a ∩ (a → a) → a, b : ■
-->{ Rule: GCTVar          }
   ⋅, f : ∀a. a ∩ (a → a) → a
-->{ Rule: GCVar           }

