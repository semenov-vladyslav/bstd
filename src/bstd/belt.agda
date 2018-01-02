module bstd.belt where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ)
-- open import Agda.Builtin.Word using (Word64)

record traits : Set₁ where
  infixl 5 _⊕_
  infixl 6 _⊞_ _⊟_
  field
    w : Set
    _⊟_ : w → w → w
    _⊞_ : w → w → w
    _⊕_ : w → w → w
    G_ : ℕ → w → w
    _⋘_ : w → ℕ → w

module prim (t : traits) where

  open traits t
  record block : Set where
    constructor _∶_∶_∶_
    field
      a b c d : w

  record key : Set where

  G₅ = G 5
  G₁₃ = G 13
  G₂₁ = G 21

  encᵢ : w → (ℕ → w) → block → block
  encᵢ i k (a ∶ b ∶ c ∶ d) = b‴ ∶ d′ ∶ a′ ∶ c‴ where
    b′ = b ⊕ G₅ (a ⊞ k 0)
    c′ = c ⊕ G₂₁ (d ⊞ k 1)
    a′ = a ⊟ G₁₃ (b ⊞ k 2)
    e = G₂₁ (b ⊞ c ⊞ k 3) ⊕ i
    b″ = b′ ⊞ e
    c″ = c′ ⊟ e
    d′ = d ⊞ G₁₃ (c ⊞ k 4)
    b‴ = b″ ⊕ G₂₁ (a ⊞ k 5)
    c‴ = c″ ⊕ G₅ (d ⊞ k 6)

  𝔼 : key → block → block
  𝔼 k b = {!encᵢ 2 k (encᵢ 1 k x))!}

{-
0 B1 94 BA C8 0A 08 F5 3B 36 6D 00 8E 58 4A 5D E4
1 85 04 FA 9D 1B B6 C7 AC 25 2E 72 C2 02 FD CE 0D
2 5B E3 D6 12 17 B9 61 81 FE 67 86 AD 71 6B 89 0B
3 5C B0 C0 FF 33 C3 56 B8 35 C4 05 AE D8 E0 7F 99
4 E1 2B DC 1A E2 82 57 EC 70 3F CC F0 95 EE 8D F1
5 C1 AB 76 38 9F E6 78 CA F7 C6 F8 60 D5 BB 9C 4F
6 F3 3C 65 7B 63 7C 30 6A DD 4E A7 79 9E B2 3D 31
7 3E 98 B5 6E 27 D3 BC CF 59 1E 18 1F 4C 5A B7 93
8 E9 DE E7 2C 8F 0C 0F A6 2D DB 49 F4 6F 73 96 47
9 06 07 53 16 ED 24 7A 37 39 CB A3 83 03 A9 8B F6
A 92 BD 9B 1C E5 D1 41 01 54 45 FB C9 5E 4D 0E F2
B 68 20 80 AA 22 7D 64 2F 26 87 F9 34 90 40 55 11
C BE 32 97 13 43 FC 9A 48 A0 2A 88 5F 19 4B 09 A1
D 7E CD A4 D0 15 44 AF 8C A5 84 50 BF 66 D2 E8 8A
E A2 D7 46 52 42 A8 DF B3 69 74 C5 51 EB 23 29 21
F D4 EF D9 B4 3A 62 28 75 91 14 10 EA 77 6C DA 1D
-}
