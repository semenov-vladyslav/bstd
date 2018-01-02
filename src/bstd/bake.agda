module bstd.bake where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Data.Word8.Primitive
open import Data.ByteString.Primitive.Strict
open import Data.Tuple.Base

module bpace
  (Scalar : Set)
  (Point : Set)
  (scalarMul : Scalar → Point → Point)
  (2ᴸ : Set)
  (Key : Set)
  (enc dec : Key → 2ᴸ → 2ᴸ)
  (swu : 2ᴸ → 2ᴸ → Point)
  (Hello : Set)
  (I : Set) (i₀ i₁ : I)
  (kdf : (K Vᵃ Vᵇ : Point) (helloᵃ helloᵇ : Hello) → I → Key)
  (Tag : Set)
  (mac : Key → I → Tag)
  where

  s₂ : (K₂ : Key)
    → (Rᵇ : 2ᴸ)
    → 2ᴸ
  s₂ K₂ Rᵇ = Yᵇ where
    Yᵇ = enc K₂ Rᵇ

  s₃ : (K₂ : Key)
    → (Rᵃ : 2ᴸ) → (uᵃ : Scalar)
    → (Yᵇ : 2ᴸ)
    → 2ᴸ ∥ Point
  s₃ K₂ Rᵃ uᵃ Yᵇ = Yᵃ , Vᵃ where
    Rᵇ = dec K₂ Yᵇ
    Yᵃ = enc K₂ Rᵃ
    W = swu Rᵃ Rᵇ
    Vᵃ = scalarMul uᵃ W

  s₄ : (K₂ : Key)
    → (Rᵇ : 2ᴸ) → (uᵇ : Scalar) → (helloᵇ : Hello)
    → (Yᵃ : 2ᴸ) → (Vᵃ : Point) → (helloᵃ : Hello)
    → Point ∥ Tag
  s₄ K₂ Rᵇ uᵇ helloᵇ Yᵃ Vᵃ helloᵃ = Vᵇ , Tᵇ where
    Rᵃ = dec K₂ Yᵃ
    W = swu Rᵃ Rᵇ
    Vᵇ = scalarMul uᵇ W
    K = scalarMul uᵇ Vᵃ
    K₀ = kdf K Vᵃ Vᵇ helloᵃ helloᵇ i₀
    K₁ = kdf K Vᵃ Vᵇ helloᵃ helloᵇ i₁
    Tᵇ = mac K₁ i₁

  s₅ : (Vᵇ : Point) → (helloᵇ : Hello)
    → (uᵃ : Scalar) → (Vᵃ : Point) → (helloᵃ : Hello)
    → Tag
  s₅ Vᵇ helloᵇ uᵃ Vᵃ helloᵃ = Tᵃ where
    K = scalarMul uᵃ Vᵇ
    K₀ = kdf K Vᵃ Vᵇ helloᵃ helloᵇ i₀
    K₁ = kdf K Vᵃ Vᵇ helloᵃ helloᵇ i₁
    Tᵃ = mac K₁ i₀
