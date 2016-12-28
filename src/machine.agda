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

-- Thanks to Conor McBride's metaprogramming notes, we have some stuff
-- for plugging a value into a zipper; this can be thought of like unloading
-- a control stack.
module Plug {S O} (⊢Σ : Sig S O) (ar/≡? : {j : O} (ϑ : op ⊢Σ j) (α β : ar ⊢Σ (j ▸ ϑ)) → Decidable (α ≡ β)) where
  plug : ∀ {i j X} → ⟦ ∇ ⊢Σ ⟧◃ X (j , i) → X i → ⟦ ⊢Σ ⟧◃ X j
  plug {X = X} ((ϑ ▸ α ▸ p) ▸ tail) x = ϑ ▸ aux
    where
      aux : (β : ar ⊢Σ (_ ▸ ϑ)) → X (so ⊢Σ ((_ ▸ ϑ) ▸ β))
      aux β with ar/≡? ϑ α β
      aux β | ⊕.inl p = tail (β ▸ p)
      aux β | ⊕.inr p′ = ≡.coe* X (p ≡.⁻¹ ≡.⟓ _ ≡.· p′) x

module Unload {S} (⊢Σ : Sig S S) (ar/≡? : {i : S} (ϑ : op ⊢Σ i) (α β : ar ⊢Σ (i ▸ ϑ)) → Decidable (α ≡ β)) where
  open Plug ⊢Σ ar/≡?
  unload : {i j : S} → W.W (Zipper ⊢Σ) (i , j) → W.W ⊢Σ j → W.W ⊢Σ i
  unload (W.sup (⊕.inl refl) tail) t = t
  unload (W.sup (⊕.inr (_ ▸ c)) tail) t =
    let hd ▸ tl = plug {X = W.W ⊢Σ} c t
    in unload (tail *) (W.sup hd tl)


module Λ where
  data Sort : Set where
    exp val : Sort

  record Seq : Set where
    no-eta-equality
    constructor _⊢_
    field
      vars : Nat
      sort : Sort

  -- Operators
  data Op : Seq → Set where
    var : ∀ {𝒳} → Fin 𝒳 → Op (𝒳 ⊢ val)
    lam : ∀ {𝒳} → Op (𝒳 ⊢ val)
    ap : ∀ {𝒳} → Op (𝒳 ⊢ exp)
    ret : ∀ {𝒳} → Op (𝒳 ⊢ exp)

  -- Argument slots in application terms
  data ApSlot : Set where
    fun arg : ApSlot

  sig : Sig Seq Seq
  op sig = Op
  ar sig (𝒳 ⊢ .val ▸ var x) = 𝟘
  ar sig (𝒳 ⊢ .val ▸ lam) = 𝟙
  ar sig (𝒳 ⊢ .exp ▸ ap) = ApSlot
  ar sig (𝒳 ⊢ .exp ▸ ret) = 𝟙
  so sig ((_ ▸ var x) ▸ ())
  so sig ((𝒳 ⊢ .val ▸ lam) ▸ *) = (su 𝒳) ⊢ exp
  so sig (((𝒳 ⊢ .exp) ▸ ap) ▸ fun) = 𝒳 ⊢ exp
  so sig (((𝒳 ⊢ .exp) ▸ ap) ▸ arg) = 𝒳 ⊢ exp
  so sig (((𝒳 ⊢ .exp) ▸ ret) ▸ *) = 𝒳 ⊢ val

  ar≡? : {j : _} (ϑ : op sig j) (α β : ar sig (j ▸ ϑ)) → Decidable (α ≡ β)
  ar≡? (var x) () β
  ar≡? lam _ _ = ⊕.inr refl
  ar≡? ap fun fun = ⊕.inr refl
  ar≡? ap fun arg = ⊕.inl λ { () }
  ar≡? ap arg fun = ⊕.inl λ { () }
  ar≡? ap arg arg = ⊕.inr refl
  ar≡? ret _ _ = ⊕.inr refl

  open Unload sig ar≡? public

  module Notation where
    Tm : Seq → Set
    Tm = W.W sig

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

  module _ where
    open Notation

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

open Λ.Notation
open Λ using (ap; fun; arg; lam; var; ret; exp; val; _⊢_)

Stk : Set
Stk = W.W (Zipper Λ.sig) (0 ⊢ exp , 0 ⊢ exp)


-- Patterns for control stacks
pattern nil ρ = W.sup (⊕.inl refl) ρ
pattern _[_,_]_∷_ ϑ α p ρ stk = W.sup (⊕.inr (_ ⊢ _ ▸ (ϑ ▸ (α ▸ p)) ▸ ρ)) stk


-- Some shortcuts for pushing stack frames
ap[-,_]∷_ : Exp 0 → Stk → Stk
ap[-, m ]∷ stk = ap [ fun , refl ] (λ { (fun ▸ ✠) → 𝟘.¡ (✠ refl) ; (arg ▸ _) → m }) ∷ λ _ → stk

ap[_,-]∷_ : Val 0 → Stk → Stk
ap[ v ,-]∷ stk = ap [ arg , refl ] (λ { (fun ▸ _) → `ret v ; (arg ▸ ✠) → 𝟘.¡ (✠ refl) }) ∷ λ _ → stk


-- Machine configurations
data Cfg : Set where
  _◁_ : (m : Exp 0) → (stk : Stk) → Cfg
  _▷_ : (v : Val 0) → (stk : Stk) → Cfg


infixr 4 _◁_ _▷_
infix 0 go_

data Step : Set where
  go_ : Cfg → Step
  retn_ : Val 0 → Step
  stuck_ : Cfg → Step


step : Cfg → Step
step (W.sup ap ρ ◁ stk) = go ρ fun ◁ ap[-, ρ arg ]∷ stk
step (W.sup ret ρ ◁ stk) = go ρ * ▷ stk
step (v ▷ nil _) = retn v
step (v ▷ ap [ fun , refl ] ρ ∷ stk) = go ρ (arg ▸ λ { () }) ◁ ap[ v ,-]∷ stk *
step (v ▷ ap [ arg , refl ] ρ ∷ stk) with ρ (fun ▸ λ { () })
... | W.sup ap _ = stuck (v ▷ ap [ arg , refl ] ρ ∷ stk)
... | W.sup ret ret/ρ with ret/ρ *
... | W.sup lam lam/ρ = go Λ.inst (lam/ρ *) v ◁ stk *
... | W.sup (var ()) tail
step (v ▷ var _ [ () , _ ] _ ∷ _)
step (v ▷ lam [ _ , () ] _ ∷ _)
step (v ▷ ret [ _ , () ] _ ∷ _)


step* : Step → Step
step* (go x) = step x
step* (retn v) = retn v
step* (stuck e) = stuck e

cfg/unload : Cfg → Exp 0
cfg/unload (m ◁ stk) = Λ.unload stk m
cfg/unload (v ▷ stk) = Λ.unload stk (`ret v)

step/unload : Step → Exp 0
step/unload (go 𝒞) = cfg/unload 𝒞
step/unload (retn v) = `ret v
step/unload (stuck 𝒞) = cfg/unload 𝒞


init : Exp 0 → Cfg
init m = m ◁ nil λ { () }

steps : Cfg → Stream Step
steps 𝒞 = Stream.unfold (go 𝒞) (λ 𝒞′ → 𝒞′ , step* 𝒞′)

eval : Exp 0 → Stream Step
eval e = steps (init e)

module Ex where
  [id] : ∀ {𝒳} → Exp 𝒳
  [id] = `ret (`lam (`ret (`var ze)))

  test = step/unload (Stream.idx (eval (`ap [id] [id])) 10)

