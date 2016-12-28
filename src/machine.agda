{-# OPTIONS --rewriting #-}

module machine where

open import Prelude.Path
open import Prelude.Monoidal
open import Prelude.Signature.Indexed
open import Prelude.Signature.Indexed.Tree.Wellfounded
open import Prelude.List
open import Prelude.Natural
open import Prelude.Finite
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Stream

module Plug {S O} (⊢Σ : Sig S O) (ar/≡? : (j : O) (ϑ : op ⊢Σ j) (α β : ar ⊢Σ (j ▸ ϑ)) → Decidable (α ≡ β)) where
  plug : ∀ {i j X} → ⟦ ∇ ⊢Σ ⟧◃ X (j , i) → X i → ⟦ ⊢Σ ⟧◃ X j
  plug {X = X} ((ϑ ▸ α ▸ p) ▸ tail) x = ϑ ▸ aux
    where
      aux : (β : ar ⊢Σ (_ ▸ ϑ)) → X (so ⊢Σ ((_ ▸ ϑ) ▸ β))
      aux β with ar/≡? _ ϑ α β
      aux β | ⊕.inl p = tail (β ▸ p)
      aux β | ⊕.inr p′ = ≡.coe* X (p ≡.⁻¹ ≡.⟓ _ ≡.· p′) x

module Unload {S} (⊢Σ : Sig S S) (ar/≡? : (i : S) (ϑ : op ⊢Σ i) (α β : ar ⊢Σ (i ▸ ϑ)) → Decidable (α ≡ β)) where
  unload : {i j : S} → W.W (Zipper ⊢Σ) (i , j) → W.W ⊢Σ j → W.W ⊢Σ i
  unload (W.sup (⊕.inl refl) tail) t = t
  unload (W.sup (⊕.inr (_ ▸ c)) tail) t =
    let hd ▸ tl = Plug.plug ⊢Σ ar/≡? {X = W.W ⊢Σ} c t
    in unload (tail *) (W.sup hd tl)

data ⊢Λ/Sort : Set where
  exp val : ⊢Λ/Sort

record ⊢Λ/Seq : Set where
  no-eta-equality
  constructor _⊢_
  field
    vars : Nat
    sort : ⊢Λ/Sort

data ⊢Λ/op : ⊢Λ/Seq → Set where
  var : ∀ {𝒳} → Fin 𝒳 → ⊢Λ/op (𝒳 ⊢ val)
  lam : ∀ {𝒳} → ⊢Λ/op (𝒳 ⊢ val)
  ap : ∀ {𝒳} → ⊢Λ/op (𝒳 ⊢ exp)
  ret : ∀ {𝒳} → ⊢Λ/op (𝒳 ⊢ exp)

data ⊢Λ/ap/slot : Set where
  fun arg : ⊢Λ/ap/slot

⊢Λ : Sig ⊢Λ/Seq ⊢Λ/Seq
op ⊢Λ = ⊢Λ/op
ar ⊢Λ (𝒳 ⊢ .val ▸ var x) = 𝟘
ar ⊢Λ (𝒳 ⊢ .val ▸ lam) = 𝟙
ar ⊢Λ (𝒳 ⊢ .exp ▸ ap) = ⊢Λ/ap/slot
ar ⊢Λ (𝒳 ⊢ .exp ▸ ret) = 𝟙
so ⊢Λ ((_ ▸ var x) ▸ ())
so ⊢Λ ((𝒳 ⊢ .val ▸ lam) ▸ *) = (su 𝒳) ⊢ exp
so ⊢Λ (((𝒳 ⊢ .exp) ▸ ap) ▸ fun) = 𝒳 ⊢ exp
so ⊢Λ (((𝒳 ⊢ .exp) ▸ ap) ▸ arg) = 𝒳 ⊢ exp
so ⊢Λ (((𝒳 ⊢ .exp) ▸ ret) ▸ *) = 𝒳 ⊢ val

Tm : ⊢Λ/Seq → Set
Tm = W.W ⊢Λ

Exp : Nat → Set
Exp 𝒳 = Tm (𝒳 ⊢ exp)

Val : Nat → Set
Val 𝒳 = Tm (𝒳 ⊢ val)


`var : ∀ {𝒳} → Fin 𝒳 → Val 𝒳
`var x = W.sup (var x) (λ α → 𝟘.¡ α)


`ap : ∀ {𝒳} → Exp 𝒳 → Exp 𝒳 → Exp 𝒳
`ap m n = W.sup ap λ { fun → m ; arg → n }


`lam : ∀ {𝒳} → Exp (su 𝒳) → Val 𝒳
`lam m = W.sup lam λ { * → m }

`ret : ∀ {𝒳} → Val 𝒳 → Exp 𝒳
`ret m = W.sup ret λ { * → m }

wk : ∀ {𝒳 τ} → Tm (𝒳 ⊢ τ) → Tm ((su 𝒳) ⊢ τ)
wk (W.sup (var x) ρ) = `var (su x)
wk (W.sup lam ρ) = `lam (wk (ρ *))
wk (W.sup ap ρ) = `ap (wk (ρ fun)) (wk (ρ arg))
wk (W.sup ret ρ) = `ret (wk (ρ *))

inst : ∀ {𝒳 τ} → Tm ((su 𝒳) ⊢ τ) → Val 𝒳 → Tm (𝒳 ⊢ τ)
inst (W.sup (var ze) _) v = v
inst (W.sup (var (su x)) _) v = `var x
inst (W.sup lam ρ) v = `lam (inst (ρ *) (wk v))
inst (W.sup ap ρ) v = `ap (inst (ρ fun) v) (inst (ρ arg) v)
inst (W.sup ret ρ) v = `ret (inst (ρ *) v)

Stk : Set
Stk = W.W (Zipper ⊢Λ) (0 ⊢ exp , 0 ⊢ exp)


data Cfg : Set where
  _◁_ : (m : Exp 0) → (stk : Stk) → Cfg
  _▷_ : (m : Val 0) → (stk : Stk) → Cfg

infixr 4 _◁_ _▷_
infix 0 go_

data Step (A B : Set) : Set where
  go_ : A → Step A B
  return : B → Step A B
  stuck : Step A B

pattern _[_,_]_∷_ ϑ α p ρ stk = W.sup (⊕.inr (_ ⊢ _ ▸ (ϑ ▸ (α ▸ p)) ▸ ρ)) stk
pattern nil ρ = W.sup (⊕.inl refl) ρ

κ : {X Y : Set} → X → Y → X
κ x _ = x

step : Cfg → Step Cfg (Val 0)
step (W.sup ap ρ ◁ stk) = go ρ fun ◁ ap [ fun , refl ] (λ { (fun ▸ ✠) → 𝟘.¡ (✠ refl) ; (arg ▸ _) → ρ arg }) ∷ (κ stk)
step (W.sup ret ρ ◁ stk) = go ρ * ▷ stk
step (m ▷ nil _) = return m
step (m ▷ ap [ fun , refl ] ρ ∷ stk) = go ρ (arg ▸ λ { () }) ◁ ap [ arg , refl ] (λ { (fun ▸ _) → `ret m ; (arg ▸ ✠) → 𝟘.¡ (✠ refl) }) ∷ stk
step (m ▷ ap [ arg , refl ] ρ ∷ stk) with ρ (fun ▸ λ { () })
... | W.sup ap _ = stuck
... | W.sup ret ret/ρ with ret/ρ *
... | W.sup (var ()) tail
... | W.sup lam lam/ρ = go inst (lam/ρ *) m ◁ stk *
step (m ▷ var _ [ () , _ ] _ ∷ _)
step (m ▷ lam [ _ , () ] _ ∷ _)
step (m ▷ ret [ _ , () ] _ ∷ _)

step* : Step Cfg (Val 0) → Step Cfg (Val 0)
step* (go x) = step x
step* (return v) = return v
step* stuck = stuck

init : Exp 0 → Cfg
init m = m ◁ nil λ { () }

steps : Cfg → Stream (Step Cfg (Val 0))
steps 𝒞 = Stream.unfold (go 𝒞) (λ 𝒞′ → 𝒞′ , step* 𝒞′)

eval : Exp 0 → Stream (Step Cfg (Val 0))
eval e = steps (init e)

[id] : ∀ {𝒳} → Val 𝒳
[id] = `lam (`ret (`var ze))

test = Stream.idx (eval (`ap (`ret [id]) (`ret [id]))) 100
