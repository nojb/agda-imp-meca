open import IMP
open import Data.List
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
import Data.Nat
import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Properties using (length-++; ++-assoc)
open import Data.Integer.Properties using (+-assoc; suc-pred; pred-suc; suc-+)
open import Function using (_∘_)

data Instr : Set where
  Iconst : (n : ℤ) → Instr
  Ivar : (x : Id) → Instr
  Isetvar : (x : Id) → Instr
  Iadd : Instr
  Iopp : Instr
  Ibranch : (d : ℤ) → Instr
  Ibeq : (d1 : ℤ) (d0 : ℤ) → Instr
  Ible : (d1 : ℤ) (d0 : ℤ) → Instr
  Ihalt : Instr

Code : Set
Code = List Instr

codelen : Code → ℤ
codelen C = + (Data.List.length C)

codelenApp : ∀ n C₁ {C₂} → n + codelen (C₁ ++ C₂) ≡ n + codelen C₁ + codelen C₂
codelenApp n C₁ {C₂} =
  begin
    n + codelen (C₁ ++ C₂)
  ≡⟨ cong (_+_ n) (cong +_ (Data.List.Properties.length-++ C₁ {C₂})) ⟩
    n + (codelen C₁ + codelen C₂)
  ≡⟨ sym (+-assoc n (codelen C₁) (codelen C₂)) ⟩
    n + codelen C₁ + codelen C₂
  ∎

data InstrAt : Code → ℤ → Instr → Set where

  instr-at-head : ∀ {i C C' pc} →
    C ≡ i ∷ C' →
    pc ≡ 0ℤ →
    InstrAt C pc i

  instr-at-tail : ∀ {i i₁ C C' pc pc'} →
    C' ≡ i₁ ∷ C →
    pc' ≡ suc pc →
    InstrAt C pc i →
    InstrAt C' pc' i

instrAtApp : ∀ {C} C₁ {C₂ i pc} → C ≡ C₁ ++ i ∷ C₂ → pc ≡ codelen C₁ → InstrAt C pc i
instrAtApp [] HC Hpc = instr-at-head HC Hpc
instrAtApp {_} (i₁ ∷ C₁) {C₂} {i} {pc} HC Hpc =
  instr-at-tail HC (sym (suc-pred pc))
    (instrAtApp C₁ refl
      (begin
        pred pc
      ≡⟨ cong pred Hpc ⟩
        pred (codelen (i₁ ∷ C₁))
      ≡⟨ pred-suc _ ⟩
        codelen C₁
      ∎))

Stack : Set
Stack = List ℤ

record Config : Set where
  constructor _,_,_
  field
    pc : ℤ
    σ : Stack
    s : Store

data Transition (C : Code) : Config → Config → Set where

  const : ∀ {pc σ s n} →
    InstrAt C pc (Iconst n) →
    Transition C (pc , σ , s) ((pc + 1ℤ) , n ∷ σ , s)
  var : ∀ {pc σ s x} →
    InstrAt C pc (Ivar x) →
    Transition C (pc , σ , s) ((pc + 1ℤ) , s x ∷ σ , s)
  setvar : ∀ {pc} σ s {x} n →
    InstrAt C pc (Isetvar x) →
    Transition C (pc , n ∷ σ , s) ((pc + 1ℤ) , σ , update x n s)
  add : ∀ {pc σ s n1 n2 pc' σ' σ''} →
    InstrAt C pc Iadd →
    pc' ≡ pc + 1ℤ →
    σ' ≡ n2 ∷ n1 ∷ σ →
    σ'' ≡ (n1 + n2) ∷ σ →
    Transition C (pc , σ' , s) (pc' , σ'' , s)
  opp : ∀ {pc σ s n pc' σ₁ σ₂} →
    InstrAt C pc Iopp →
    pc' ≡ pc + 1ℤ →
    σ₁ ≡ n ∷ σ →
    σ₂ ≡ (- n) ∷ σ →
    Transition C (pc , σ₁ , s) (pc' , σ₂ , s)
  branch : ∀ {pc σ s d pc'} →
    InstrAt C pc (Ibranch d) →
    pc' ≡ pc + 1ℤ + d →
    Transition C (pc , σ , s) (pc' , σ , s)
  beq : ∀ {pc σ s d₁ d₀ n₁ n₂ pc'} →
    InstrAt C pc (Ibeq d₁ d₀) →
    pc' ≡ pc + 1ℤ + (if does (n₁ ≟ n₂) then d₁ else d₀) →
    Transition C (pc , n₂ ∷ n₁ ∷ σ , s) (pc' , σ , s)
  ble : ∀ {pc σ s d₁ d₀ n₁ n₂ pc'} →
    InstrAt C pc (Ible d₁ d₀) →
    pc' ≡ pc + 1ℤ + (if does (n₁ ≤? n₂) then d₁ else d₀) →
    Transition C (pc , n₂ ∷ n₁ ∷ σ , s) (pc' , σ , s)

module Sequences where

  data Star {A : Set} (R : A → A → Set) : A -> A -> Set where
    refl : ∀ {a} → Star R a a
    step : ∀ {a b c} → R a b → Star R b c → Star R a c

  one : ∀ {A : Set} {R : A → A → Set} {a b : A} → R a b → Star R a b
  one Hab = step Hab refl

  star-trans : ∀ {A : Set} {R : A → A → Set} {a b : A} → Star R a b → ∀ {c} → Star R b c → Star R a c
  star-trans refl Hbc = Hbc
  star-trans (step Haz Hzb) Hbc = step Haz (star-trans Hzb Hbc)

open Sequences using (Star; one; star-trans)

Transitions : Code -> Config -> Config -> Set
Transitions C = Sequences.Star (Transition C)

compileAExp : AExp → Code
compileAExp (CONST n) = Iconst n ∷ []
compileAExp (VAR x) = Ivar x ∷ []
compileAExp (PLUS a₁ a₂) = compileAExp a₁ ++ compileAExp a₂ ++ Iadd ∷ []
compileAExp (MINUS a₁ a₂) = compileAExp a₁ ++ compileAExp a₂ ++ Iopp ∷ Iadd ∷ []

data CodeAt (C : Code) : ℤ → Code → Set where
  codeAt : ∀ C₁ {C₂ C₃ pc} →
    pc ≡ codelen C₁ →
    C ≡ C₁ ++ C₂ ++ C₃ →
    CodeAt C pc C₂

codeAtHead : ∀ {C pc i C'} → CodeAt C pc (i ∷ C') → InstrAt C pc i
codeAtHead (codeAt C₁ Hpc HC) = instrAtApp C₁ HC Hpc

codeAtTail : ∀ {C pc i C'} → CodeAt C pc (i ∷ C') → CodeAt C (pc + 1ℤ) C'
codeAtTail {_} {pc} {i} {C'} (codeAt C₁ Hpc HC) =
  codeAt (C₁ ++ [ i ])
    (begin
      pc + 1ℤ
    ≡⟨ cong (λ n → n + 1ℤ) Hpc ⟩
      codelen C₁ + 1ℤ
    ≡⟨ refl ⟩
      codelen C₁ + codelen [ i ]
    ≡⟨ sym (codelenApp 0ℤ C₁) ⟩
      codelen (C₁ ++ [ i ])
    ∎)
    (trans HC (sym (Data.List.Properties.++-assoc C₁ _ _)))

codeAtAppLeft : ∀ {C C₁ C₂ pc} → CodeAt C pc (C₁ ++ C₂) → CodeAt C pc C₁
codeAtAppLeft {_} {C₁} {C₂} {_} (codeAt C₀ {_} {C₃} Hpc HC) =
  codeAt C₀ Hpc (trans HC (cong (_++_ C₀) (Data.List.Properties.++-assoc C₁ C₂ C₃)))

codeAtAppRight : ∀ {C} C₁ {C₂} {pc} → CodeAt C pc (C₁ ++ C₂) → CodeAt C (pc + codelen C₁) C₂
codeAtAppRight {C} C₁ {C₂} {pc} (codeAt C₀ {_} {C₃} Hpc HC) =
  codeAt (C₀ ++ C₁) pcEq CEq
  where
    pcEq : pc + codelen C₁ ≡ codelen (C₀ ++ C₁)
    pcEq =
      begin
        pc + codelen C₁
      ≡⟨ cong (λ n → n + codelen C₁) Hpc ⟩
        codelen C₀ + codelen C₁
      ≡⟨ sym (codelenApp 0ℤ C₀) ⟩
        codelen (C₀ ++ C₁)
      ∎
    CEq =
      begin
        C
      ≡⟨ HC ⟩
        C₀ ++ (C₁ ++ C₂) ++ C₃
      ≡⟨ cong (_++_ C₀) (Data.List.Properties.++-assoc C₁ C₂ C₃) ⟩
        C₀ ++ (C₁ ++ C₂ ++ C₃)
      ≡⟨ sym (Data.List.Properties.++-assoc C₀ C₁ (C₂ ++ C₃)) ⟩
        (C₀ ++ C₁) ++ C₂ ++ C₃
      ∎

codeAtAppRight2 : ∀ {C} C₁ {C₂} {C₃} {pc} → CodeAt C pc (C₁ ++ C₂ ++ C₃) → CodeAt C (pc + codelen C₁) C₂
codeAtAppRight2 C₁ H = codeAtAppLeft (codeAtAppRight C₁ H)

compileAExpCorrect : ∀ {C} {s} a {pc} {σ} →
  CodeAt C pc (compileAExp a) →
  Transitions C (pc , σ , s) ((pc + codelen (compileAExp a)) , aeval a s ∷ σ , s)

compileAExpCorrect (CONST _) H = one (const (codeAtHead H))

compileAExpCorrect (VAR _) H = one (var (codeAtHead H))

compileAExpCorrect {_} {_} (PLUS a₁ a₂) {pc} H =
  let C₁ = compileAExp a₁ in
  let C₂ = compileAExp a₂ in
  star-trans (compileAExpCorrect a₁ (codeAtAppLeft H))
    (star-trans (compileAExpCorrect a₂ (codeAtAppRight2 C₁ H))
      (one (add
        (codeAtHead (codeAtAppRight C₂ (codeAtAppRight C₁ H)))
        (begin
            pc + codelen (C₁ ++ C₂ ++ _)
          ≡⟨ codelenApp pc C₁ ⟩
            pc + codelen C₁ + codelen (C₂ ++ _)
          ≡⟨ codelenApp (pc + codelen C₁) C₂ ⟩
            pc + codelen C₁ + codelen C₂ + 1ℤ
          ∎) refl refl)))

compileAExpCorrect {_} {_} (MINUS a₁ a₂) {pc} H =
  let C₁ = compileAExp a₁ in
  let C₂ = compileAExp a₂ in
  star-trans (compileAExpCorrect a₁ (codeAtAppLeft H))
    (star-trans (compileAExpCorrect a₂ (codeAtAppLeft (codeAtAppRight C₁ H)))
      (star-trans
        (one (opp (codeAtHead (codeAtAppRight C₂ (codeAtAppRight C₁ H))) refl refl refl))
        (one (add
          (codeAtHead (codeAtTail (codeAtAppRight C₂ (codeAtAppRight C₁ H))))
          (begin
            pc + codelen (C₁ ++ C₂ ++ _)
          ≡⟨ codelenApp pc C₁ ⟩
            pc + codelen C₁ + codelen (C₂ ++ _)
          ≡⟨ codelenApp (pc + codelen C₁) C₂ ⟩
            pc + codelen C₁ + codelen C₂ + (1ℤ + 1ℤ)
          ≡⟨ sym (+-assoc (pc + codelen C₁ + codelen C₂) 1ℤ 1ℤ) ⟩
            pc + codelen C₁ + codelen C₂ + 1ℤ + 1ℤ
          ∎) refl refl))))
