module IMP where

open import Data.String using (String)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Sum
open import Data.Bool using (true; false; not; Bool; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (not-involutive)
open import Relation.Nullary public
open import Data.Nat using (ℕ)
open import Data.Integer public

Id : Set
Id = String

data AExp : Set where
  CONST : ℤ → AExp
  VAR : (x : Id) → AExp
  PLUS : (a1 a2 : AExp) → AExp
  MINUS : (a1 a2 : AExp) → AExp

Store : Set
Store = Id → ℤ

aeval : AExp → Store → ℤ
aeval (CONST n) _ = n
aeval (VAR x) s  = s x
aeval (PLUS a1 a2) s = aeval a1 s + aeval a2 s
aeval (MINUS a1 a2) s = aeval a1 s - aeval a2 s

-- _ = aeval (PLUS (VAR "x") (MINUS (VAR "x") (CONST (+ 1)))) (λ _ → + 2) ≡ + 3
-- _ = {!!}

data FreeVar (x : Id) : AExp -> Set where
  free-var : FreeVar x (VAR x)
  free-plus : ∀ a1 a2 → FreeVar x a1 ⊎ FreeVar x a2 → FreeVar x (PLUS a1 a2)
  free-minus : ∀ a1 a2 → FreeVar x a1 ⊎ FreeVar x a2 → FreeVar x (MINUS a1 a2)

aeval-free : ∀ {s1 s2} a → (∀ x → FreeVar x a → s1 x ≡ s2 x) → aeval a s1 ≡ aeval a s2
aeval-free (CONST _) _ = refl
aeval-free (VAR x) H = H x free-var
aeval-free (PLUS a1 a2) H =
  cong₂ _+_ (aeval-free a1 (λ x F → H x (free-plus a1 a2 (inj₁ F)))) (aeval-free a2 λ x z → H x (free-plus a1 a2 (inj₂ z)))
aeval-free (MINUS a1 a2) H =
  cong₂ _-_ (aeval-free a1 (λ x F → H x (free-minus a1 a2 (inj₁ F)))) (aeval-free a2 λ x z → H x (free-minus a1 a2 (inj₂ z)))

data BExp : Set where
  TRUE : BExp
  FALSE : BExp
  EQUAL : (a1 a2 : AExp) → BExp
  LESSEQUAL : (a1 a2 : AExp) → BExp
  NOT : (b1 : BExp) → BExp
  AND : (b1 b2 : BExp) → BExp

beval : BExp -> Store -> Bool
beval TRUE _ = true
beval FALSE _ = false
beval (EQUAL a1 a2) s = does (aeval a1 s ≟ aeval a2 s)
beval (LESSEQUAL a1 a2) s = does (aeval a1 s ≤? aeval a2 s)
beval (NOT b1) s = not (beval b1 s)
beval (AND b1 b2) s = beval b1 s ∧ beval b2 s

NOTEQUAL : AExp → AExp → BExp
NOTEQUAL a1 a2 = NOT (EQUAL a1 a2)

GREATEREQUAL : AExp → AExp → BExp
GREATEREQUAL a1 a2 = LESSEQUAL a2 a1

GREATER : AExp → AExp → BExp
GREATER a1 a2 = NOT (LESSEQUAL a1 a2)

LESS : AExp → AExp → BExp
LESS a1 a2 = GREATER a2 a1

OR : BExp → BExp → BExp
OR b1 b2 = NOT (AND (NOT b1) (NOT b2))

not-distrib : ∀ b1 b2 → not b1 ∧ not b2 ≡ not (b1 ∨ b2)
not-distrib false _ = refl
not-distrib true _ = refl

beval_OR : ∀ s b1 b2 → beval (OR b1 b2) s ≡ beval b1 s ∨ beval b2 s
beval_OR s b1 b2 =
  begin
    beval (OR b1 b2) s
  ≡⟨⟩
    not (not (beval b1 s) ∧ not (beval b2 s))
  ≡⟨ cong not (not-distrib (beval b1 s) (beval b2 s)) ⟩
    not (not (beval b1 s ∨ beval b2 s))
  ≡⟨ not-involutive _ ⟩
    beval b1 s ∨ beval b2 s
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
    WHILE b c / s' ⇓ s''

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
