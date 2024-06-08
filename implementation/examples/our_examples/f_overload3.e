(((\x -> \y -> x) :: (Int -> Int -> Int) /\ (Int -> Bool -> Int)) 1) True

-- Accepted!
--    ⋅ ⊩ ((λx. λy. x :: (Int → Int → Int) ∩ (Int → Bool → Int)) 1) True ⇒a End
-- -->{ Rule: ⇒App            }
--    ⋅ ⊩ (λx. λy. x :: (Int → Int → Int) ∩ (Int → Bool → Int)) 1 ⇒b b ▹c,a0 c → a0 ⊙ True ➤a End
-- -->{ Rule: ⇒App            }
--    ⋅ ⊩ λx. λy. x :: (Int → Int → Int) ∩ (Int → Bool → Int) ⇒b0 b0 ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End
-- -->{ Rule: ⇒Anno           }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End ⊩ λx. λy. x ⇐ (Int → Int → Int) ∩ (Int → Bool → Int)
-- -->{ Rule: ⇐∩              }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End ⊩ λx. λy. x ⇐ Int → Int → Int ⊩ λx. λy. x ⇐ Int → Bool → Int
-- -->{ Rule: ⇐λ              }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End ⊩ λx. λy. x ⇐ Int → Int → Int, x0 : Int ⊩ λy. x0 ⇐ Bool → Int
-- -->{ Rule: ⇐λ              }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End ⊩ λx. λy. x ⇐ Int → Int → Int, x0 : Int, y0 : Bool ⊩ x0 ⇐ Int
-- -->{ Rule: ⇐Sub            }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End ⊩ λx. λy. x ⇐ Int → Int → Int, x0 : Int, y0 : Bool ⊩ x0 ⇒b0 b0 ≤ Int
-- -->{ Rule: ⇒Var            }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End ⊩ λx. λy. x ⇐ Int → Int → Int, x0 : Int, y0 : Bool ⊩ Int ≤ Int
-- -->{ Rule: ≤Int            }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End ⊩ λx. λy. x ⇐ Int → Int → Int, x0 : Int, y0 : Bool
-- -->{ Rule: GCVar           }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End ⊩ λx. λy. x ⇐ Int → Int → Int, x0 : Int
-- -->{ Rule: GCVar           }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End ⊩ λx. λy. x ⇐ Int → Int → Int
-- -->{ Rule: ⇐λ              }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End, x0 : Int ⊩ λy. x0 ⇐ Int → Int
-- -->{ Rule: ⇐λ              }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End, x0 : Int, x : Int ⊩ x0 ⇐ Int
-- -->{ Rule: ⇐Sub            }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End, x0 : Int, x : Int ⊩ x0 ⇒b0 b0 ≤ Int
-- -->{ Rule: ⇒Var            }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End, x0 : Int, x : Int ⊩ Int ≤ Int
-- -->{ Rule: ≤Int            }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End, x0 : Int, x : Int
-- -->{ Rule: GCVar           }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End, x0 : Int
-- -->{ Rule: GCVar           }
--    ⋅ ⊩ (Int → Int → Int) ∩ (Int → Bool → Int) ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End
-- -->{ Rule: ▹∩2             }
--    ⋅ ⊩ Int → Bool → Int ▹c0,a1 c0 → a1 ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End
-- -->{ Rule: ▹→              }
--    ⋅ ⊩ Int → Bool → Int ⊙ 1 ➤b b ▹c,a0 c → a0 ⊙ True ➤a End
-- -->{ Rule: ⊙➤              }
--    ⋅ ⊩ Bool → Int ▹c,a0 c → a0 ⊙ True ➤a End ⊩ 1 ⇐ Int
-- -->{ Rule: ⇐Sub            }
--    ⋅ ⊩ Bool → Int ▹c,a0 c → a0 ⊙ True ➤a End ⊩ 1 ⇒b b ≤ Int
-- -->{ Rule: ⇒Int            }
--    ⋅ ⊩ Bool → Int ▹c,a0 c → a0 ⊙ True ➤a End ⊩ Int ≤ Int
-- -->{ Rule: ≤Int            }
--    ⋅ ⊩ Bool → Int ▹c,a0 c → a0 ⊙ True ➤a End
-- -->{ Rule: ▹→              }
--    ⋅ ⊩ Bool → Int ⊙ True ➤a End
-- -->{ Rule: ⊙➤              }
--    ⋅ ⊩ End ⊩ True ⇐ Bool
-- -->{ Rule: ⇐Sub            }
--    ⋅ ⊩ End ⊩ True ⇒a a ≤ Bool
-- -->{ Rule: ⇒Bool           }
--    ⋅ ⊩ End ⊩ Bool ≤ Bool
-- -->{ Rule: ≤Bool           }
--    ⋅ ⊩ End
-- -->{ Rule: Dummy           }