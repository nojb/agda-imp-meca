module IMP where

open import Data.String using (String)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Sum
open import Data.Bool using (true; false; not; Bool; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (not-involutive)
open import Relation.Nullary
open import Data.Nat using (ℕ)
open import Data.Integer

Id : Set
Id = String

data AExp : Set where
  CONST : ℤ → AExp
  VAR : (x : Id) → AExp
  PLUS : (a₁ a₂ : AExp) → AExp
  MINUS : (a₁ a₂ : AExp) → AExp

Store : Set
Store = Id → ℤ

aeval : AExp → Store → ℤ
aeval (CONST n) _ = n
aeval (VAR x) s  = s x
aeval (PLUS a₁ a₂) s = aeval a₁ s + aeval a₂ s
aeval (MINUS a₁ a₂) s = aeval a₁ s - aeval a₂ s

data FreeVar (x : Id) : AExp -> Set where
  free-var : FreeVar x (VAR x)
  free-plus : ∀ a₁ a₂ → FreeVar x a₁ ⊎ FreeVar x a₂ → FreeVar x (PLUS a₁ a₂)
  free-minus : ∀ a₁ a₂ → FreeVar x a₁ ⊎ FreeVar x a₂ → FreeVar x (MINUS a₁ a₂)

aeval-free : ∀ {s₁ s₂} a → (∀ x → FreeVar x a → s₁ x ≡ s₂ x) → aeval a s₁ ≡ aeval a s₂
aeval-free (CONST _) _ = refl
aeval-free (VAR x) H = H x free-var
aeval-free (PLUS a₁ a₂) H =
  cong₂ _+_ (aeval-free a₁ (λ x F → H x (free-plus a₁ a₂ (inj₁ F)))) (aeval-free a₂ λ x z → H x (free-plus a₁ a₂ (inj₂ z)))
aeval-free (MINUS a₁ a₂) H =
  cong₂ _-_ (aeval-free a₁ (λ x F → H x (free-minus a₁ a₂ (inj₁ F)))) (aeval-free a₂ λ x z → H x (free-minus a₁ a₂ (inj₂ z)))

data BExp : Set where
  TRUE : BExp
  FALSE : BExp
  EQUAL : (a₁ a₂ : AExp) → BExp
  LESSEQUAL : (a₁ a₂ : AExp) → BExp
  NOT : (b₁ : BExp) → BExp
  AND : (b₁ b₂ : BExp) → BExp

beval : BExp -> Store -> Bool
beval TRUE _ = true
beval FALSE _ = false
beval (EQUAL a₁ a₂) s = does (aeval a₁ s ≟ aeval a₂ s)
beval (LESSEQUAL a₁ a₂) s = does (aeval a₁ s ≤? aeval a₂ s)
beval (NOT b₁) s = not (beval b₁ s)
beval (AND b₁ b₂) s = beval b₁ s ∧ beval b₂ s

NOTEQUAL : AExp → AExp → BExp
NOTEQUAL a₁ a₂ = NOT (EQUAL a₁ a₂)

GREATEREQUAL : AExp → AExp → BExp
GREATEREQUAL a₁ a₂ = LESSEQUAL a₂ a₁

GREATER : AExp → AExp → BExp
GREATER a₁ a₂ = NOT (LESSEQUAL a₁ a₂)

LESS : AExp → AExp → BExp
LESS a₁ a₂ = GREATER a₂ a₁

OR : BExp → BExp → BExp
OR b₁ b₂ = NOT (AND (NOT b₁) (NOT b₂))

not-distrib : ∀ b₁ b₂ → not b₁ ∧ not b₂ ≡ not (b₁ ∨ b₂)
not-distrib false _ = refl
not-distrib true _ = refl

beval_OR : ∀ s b₁ b₂ → beval (OR b₁ b₂) s ≡ beval b₁ s ∨ beval b₂ s
beval_OR s b₁ b₂ =
  begin
    beval (OR b₁ b₂) s
  ≡⟨⟩
    not (not (beval b₁ s) ∧ not (beval b₂ s))
  ≡⟨ cong not (not-distrib (beval b₁ s) (beval b₂ s)) ⟩
    not (not (beval b₁ s ∨ beval b₂ s))
  ≡⟨ not-involutive _ ⟩
    beval b₁ s ∨ beval b₂ s
  ∎

data Com : Set where
  SKIP       : Com
  ASSIGN     : (x : Id) (a : AExp) → Com
  SEQ        : (c₁ c₂ : Com) → Com
  IFTHENELSE : (b : BExp) (c₁ c₂ : Com) → Com
  WHILE      : (b : BExp) (c : Com) → Com

update : Id → ℤ → Store → Store
update x v s = λ y → if does (Data.String._≟_ x y) then v else s y

data _/_⇓_ : Com → Store → Store → Set where
  skip : ∀ {s} →
    SKIP / s ⇓ s
  assign : ∀ {s} x a →
    ASSIGN x a / s ⇓ update x (aeval a s) s
  seq : ∀ c₁ c₂ {s s' s''} →
    c₁ / s ⇓ s' →
    c₂ / s' ⇓ s'' →
    SEQ c₁ c₂ / s ⇓ s''
  ifthenelse : ∀ b c₁ c₂ {s s'} →
    (if beval b s then c₁ else c₂) / s ⇓ s' →
    IFTHENELSE b c₁ c₂ / s ⇓ s'
  while-done : ∀ b c {s} →
    beval b s ≡ false →
    WHILE b c / s ⇓ s
  while-loop : ∀ b c {s s' s''} →
    beval b s ≡ true →
    c / s ⇓ s' →
    WHILE b c / s' ⇓ s'' →
    WHILE b c / s ⇓ s''

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished : Set where
  done :
      Store
      ----------
    → Finished

  out-of-gas :
      ----------
      Finished
