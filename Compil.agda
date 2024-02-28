open import IMP
open import Data.List as List
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; inspect)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Bool using (true; false; not; Bool; if_then_else_; T)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Data.Nat
import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Properties using (length-++; ++-assoc)
open import Data.Integer.Properties using (+-assoc; suc-pred; pred-suc; suc-+; +-identityʳ; +-identityˡ; +-comm)
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
codelen [] = 0ℤ
codelen (_ ∷ C) = suc (codelen C)

codelenApp : ∀ C₁ {C₂} → codelen (C₁ ++ C₂) ≡ codelen C₁ + codelen C₂
codelenApp [] {C₂} = sym (+-identityˡ (codelen C₂))
codelenApp (x ∷ C) {C₂} =
  begin
    suc (codelen (C ++ C₂))
  ≡⟨ cong suc (codelenApp C) ⟩
    suc (codelen C + codelen C₂)
  ≡⟨ sym (+-assoc 1ℤ (codelen C) _) ⟩
    suc (codelen C) + codelen C₂
  ∎

codelenApp' : ∀ n C₁ {C₂} → n + codelen (C₁ ++ C₂) ≡ n + codelen C₁ + codelen C₂
codelenApp' n C₁ = trans (cong (_+_ n) (codelenApp C₁)) (sym (+-assoc n (codelen C₁) _))

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
  setvar : ∀ {pc σ s x n} →
    InstrAt C pc (Isetvar x) →
    Transition C (pc , n ∷ σ , s) ((pc + 1ℤ) , σ , update x n s)
  add : ∀ {pc σ s n₁ n₂} →
    InstrAt C pc Iadd →
    Transition C (pc , n₂ ∷ n₁ ∷ σ , s) ((pc + 1ℤ) , (n₁ + n₂) ∷ σ , s)
  opp : ∀ {pc σ s n} →
    InstrAt C pc Iopp →
    Transition C (pc , n ∷ σ , s) ((pc + 1ℤ) , (- n) ∷ σ , s)
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

add' : ∀ {C pc σ s n₁ n₂ pc' σ''} →
  InstrAt C pc Iadd →
  pc' ≡ pc + 1ℤ →
  σ'' ≡ (n₁ + n₂) ∷ σ →
  Transition C (pc , n₂ ∷ n₁ ∷ σ , s) (pc' , σ'' , s)
add' H Hpc Hσ' rewrite Hpc rewrite Hσ' = add H

opp' : ∀ {C pc σ s n pc' σ₂} →
  InstrAt C pc Iopp →
  pc' ≡ pc + 1ℤ →
  σ₂  ≡ (- n) ∷ σ →
  Transition C (pc , n ∷ σ , s) (pc' , σ₂ , s)
opp' H Hpc Hσ₂ rewrite Hpc rewrite Hσ₂ = opp H

setvar' : ∀ {C pc σ s x n pc'} →
  InstrAt C pc (Isetvar x) →
  pc' ≡ pc + 1ℤ →
  Transition C (pc , n ∷ σ , s) (pc' , σ , update x n s)
setvar' H Hpc rewrite Hpc = setvar H

data Transitions (C : Code) : Config → Config → Set where
  one : ∀ {c₁ c₂} →
    Transition C c₁ c₂ →
    Transitions C c₁ c₂
  eps : ∀ {c} →
    Transitions C c c
  star-trans : ∀ {c₁ c₂ c₃} →
    Transitions C c₁ c₂ →
    Transitions C c₂ c₃ →
    Transitions C c₁ c₃

eps' : ∀ {C c₁ c₂} → c₁ ≡ c₂ → Transitions C c₁ c₂
eps' H = Eq.subst (Transitions _ _) H eps

compileAExp : AExp → Code
compileAExp (CONST n) = Iconst n ∷ []
compileAExp (VAR x) = Ivar x ∷ []
compileAExp (PLUS a₁ a₂) = compileAExp a₁ ++ compileAExp a₂ ++ Iadd ∷ []
compileAExp (MINUS a₁ a₂) = compileAExp a₁ ++ compileAExp a₂ ++ Iopp ∷ Iadd ∷ []

compile-bexp : BExp → ℤ → ℤ → Code
compile-bexp TRUE d₁ _ = if does (d₁ ≟ 0ℤ) then [] else [ Ibranch d₁ ]
compile-bexp FALSE _ d₀ = if does (d₀ ≟ 0ℤ) then [] else [ Ibranch d₀ ]
compile-bexp (EQUAL a₁ a₂) d₁ d₀ = compileAExp a₁ ++ compileAExp a₂ ++ [ Ibeq d₁ d₀ ]
compile-bexp (LESSEQUAL a₁ a₂) d₁ d₀ = compileAExp a₁ ++ compileAExp a₂ ++ [ Ible d₁ d₀ ]
compile-bexp (NOT b₁) d₁ d₀ = compile-bexp b₁ d₀ d₁
compile-bexp (AND b₁ b₂) d₁ d₀ =
  let code₂ = compile-bexp b₂ d₁ d₀ in
  let code₁ = compile-bexp b₁ 0ℤ (codelen code₂ + d₀) in
  code₁ ++ code₂

compile-com : Com → Code

compile-com SKIP         = []
compile-com (ASSIGN x a) = compileAExp a ++ Isetvar x ∷ []
compile-com (SEQ c₁ c₂)  = compile-com c₁ ++ compile-com c₂

compile-com (IFTHENELSE b ifso ifnot) =
  let code-ifso = compile-com ifso in
  let code-ifnot = compile-com ifnot in
  compile-bexp b 0ℤ (codelen code-ifso + 1ℤ)
  ++ code-ifso ++ Ibranch (codelen code-ifnot) ∷ code-ifnot

compile-com (WHILE b body) =
  let code-body = compile-com body in
  let code-test = compile-bexp b 0ℤ (codelen code-body + 1ℤ) in
  code-test ++ code-body ++ Ibranch (- (codelen code-test + codelen code-body + 1ℤ)) ∷ []

if-not : ∀ a {A : Set} {b c : A} → (if a then b else c) ≡ (if not a then c else b)
if-not false = refl
if-not true  = refl

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
    ≡⟨ cong (_+ 1ℤ) Hpc ⟩
      codelen C₁ + 1ℤ
    ≡⟨ refl ⟩
      codelen C₁ + codelen [ i ]
    ≡⟨ sym (codelenApp C₁) ⟩
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
      ≡⟨ cong (_+ codelen C₁) Hpc ⟩
        codelen C₀ + codelen C₁
      ≡⟨ sym (codelenApp C₀) ⟩
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

codeAtAppRight' : ∀ {C} C₁ {C₂} {pc} {pc'} → CodeAt C pc (C₁ ++ C₂) → pc' ≡ pc + codelen C₁ → CodeAt C pc' C₂
codeAtAppRight' C₁ H eq = Eq.subst (λ pc → CodeAt _ pc _) (sym eq) (codeAtAppRight C₁ H)

codeAtAppRight2 : ∀ {C} C₁ {C₂} {C₃} {pc} → CodeAt C pc (C₁ ++ C₂ ++ C₃) → CodeAt C (pc + codelen C₁) C₂
codeAtAppRight2 C₁ H = codeAtAppLeft (codeAtAppRight C₁ H)

compile-aexp-correct : ∀ {C} {s} a {pc} {σ} →
  CodeAt C pc (compileAExp a) →
  Transitions C (pc , σ , s) ((pc + codelen (compileAExp a)) , aeval a s ∷ σ , s)

compile-aexp-correct (CONST _) H = one (const (codeAtHead H))

compile-aexp-correct (VAR _) H = one (var (codeAtHead H))

compile-aexp-correct {_} {_} (PLUS a₁ a₂) {pc} H =
  let code₁ = compileAExp a₁ in
  let code₂ = compileAExp a₂ in
  star-trans (compile-aexp-correct a₁ (codeAtAppLeft H))
    (star-trans (compile-aexp-correct a₂ (codeAtAppRight2 code₁ H))
      (one (add'
        (codeAtHead (codeAtAppRight code₂ (codeAtAppRight code₁ H)))
        (begin
            pc + codelen (code₁ ++ code₂ ++ _)
          ≡⟨ codelenApp' pc code₁ ⟩
            pc + codelen code₁ + codelen (code₂ ++ _)
          ≡⟨ codelenApp' (pc + codelen code₁) code₂ ⟩
            pc + codelen code₁ + codelen code₂ + 1ℤ
          ∎) refl)))

compile-aexp-correct {_} {_} (MINUS a₁ a₂) {pc} H =
  let C₁ = compileAExp a₁ in
  let C₂ = compileAExp a₂ in
  star-trans (compile-aexp-correct a₁ (codeAtAppLeft H))
    (star-trans (compile-aexp-correct a₂ (codeAtAppLeft (codeAtAppRight C₁ H)))
      (star-trans
        (one (opp' (codeAtHead (codeAtAppRight C₂ (codeAtAppRight C₁ H))) refl refl))
        (one (add'
          (codeAtHead (codeAtTail (codeAtAppRight C₂ (codeAtAppRight C₁ H))))
          (begin
            pc + codelen (C₁ ++ C₂ ++ _)
          ≡⟨ codelenApp' pc C₁ ⟩
            pc + codelen C₁ + codelen (C₂ ++ _)
          ≡⟨ codelenApp' (pc + codelen C₁) C₂ ⟩
            pc + codelen C₁ + codelen C₂ + (1ℤ + 1ℤ)
          ≡⟨ sym (+-assoc (pc + codelen C₁ + codelen C₂) 1ℤ 1ℤ) ⟩
            pc + codelen C₁ + codelen C₂ + 1ℤ + 1ℤ
          ∎) refl))))

pc-correct : ∀ {C pc pc' σ s} → pc ≡ pc' → Transitions C (pc , σ , s) (pc' , σ , s)
pc-correct eq = eps' (cong (_, _ , _) eq)

compile-bexp-correct : ∀ {C s} b {d₁ d₀ pc σ} →
  CodeAt C pc (compile-bexp b d₁ d₀) →
  Transitions C
    (pc , σ , s)
    ((pc + codelen (compile-bexp b d₁ d₀) + (if beval b s then d₁ else d₀)) , σ , s)

compile-bexp-correct TRUE {d₁ = d₁} {pc = pc} H with d₁ ≟ 0ℤ
...  | yes p = pc-correct (begin
                 pc
               ≡⟨ sym (+-identityʳ _) ⟩
                 pc + 0ℤ
               ≡⟨ sym (+-identityˡ _) ⟩
                 0ℤ + (pc + 0ℤ)
               ≡⟨ cong (λ n → n + _) (sym p) ⟩
                 d₁ + (pc + 0ℤ)
               ≡⟨ +-comm d₁ (pc + 0ℤ) ⟩
                 pc + 0ℤ + d₁
               ∎)
...  | no _  = one (branch (codeAtHead H) refl)


compile-bexp-correct FALSE {d₀ = d₀} {pc = pc} H with d₀ ≟ 0ℤ
...  | yes p = pc-correct (begin
                 pc
               ≡⟨ sym (+-identityʳ _) ⟩
                 pc + 0ℤ
               ≡⟨ sym (+-identityˡ _) ⟩
                 0ℤ + (pc + 0ℤ)
               ≡⟨ cong (λ n → n + _) (sym p) ⟩
                 d₀ + (pc + 0ℤ)
               ≡⟨ +-comm d₀ (pc + 0ℤ) ⟩
                 pc + 0ℤ + d₀
               ∎)
...  | no _  = one (branch (codeAtHead H) refl)

compile-bexp-correct (EQUAL a₁ a₂) {pc = pc} H =
  let code₁ = compileAExp a₁ in
  let code₂ = compileAExp a₂ in
  star-trans (
  compile-aexp-correct a₁ (codeAtAppLeft H)) (star-trans (
  compile-aexp-correct a₂ (codeAtAppRight2 code₁ H)) (one (
  beq (codeAtHead (codeAtAppRight code₂ (codeAtAppRight code₁ H)))
  (cong (λ x → x + _) (begin
    pc + codelen(code₁ ++ code₂ ++ [ _ ])
  ≡⟨ codelenApp' pc code₁ ⟩
    pc + codelen code₁ + codelen(code₂ ++ [ _ ])
  ≡⟨ codelenApp' (pc + codelen code₁) code₂ ⟩
    pc + codelen code₁ + codelen code₂ + 1ℤ
  ∎)))))

compile-bexp-correct (LESSEQUAL a₁ a₂) {pc = pc} H =
  let code₁ = compileAExp a₁ in
  let code₂ = compileAExp a₂ in
  star-trans (
  compile-aexp-correct a₁ (codeAtAppLeft H)) (star-trans (
  compile-aexp-correct a₂ (codeAtAppRight2 code₁ H)) (one (
  ble (codeAtHead (codeAtAppRight code₂ (codeAtAppRight code₁ H)))
  (cong (λ x → x + _)
    (begin
      pc + codelen(code₁ ++ code₂ ++ [ _ ])
    ≡⟨ codelenApp' pc code₁ ⟩
      pc + codelen code₁ + codelen(code₂ ++ [ _ ])
    ≡⟨ codelenApp' (pc + codelen code₁) code₂ ⟩
      pc + codelen code₁ + codelen code₂ + 1ℤ
    ∎
    )))))

compile-bexp-correct {s = s} (NOT b) {d₁} {d₀} {pc} H =
  star-trans (
  compile-bexp-correct b {d₀} {d₁} H) (
  eps' (cong (_, _ , _) (cong (_+_ (pc + codelen (compile-bexp b d₀ d₁))) (if-not (beval b s)))))

compile-bexp-correct {s = s} (AND b₁ b₂) {d₁} {d₀} {pc} H with beval b₁ s in eq
... | true =
           let code₂ = compile-bexp b₂ d₁ d₀ in
           let code₁ = compile-bexp b₁ 0ℤ (codelen code₂ + d₀) in
           star-trans (
           compile-bexp-correct b₁ (codeAtAppLeft H)) (star-trans (
           compile-bexp-correct b₂ (codeAtAppRight' code₁ H
             (begin (
               pc + codelen code₁ + (if beval b₁ s then 0ℤ else codelen code₂ + d₀)
             ≡⟨ cong (λ b → pc + codelen code₁ + (if b then _ else _)) eq ⟩
               pc + codelen code₁ + 0ℤ
             ≡⟨ +-identityʳ _ ⟩
               pc + codelen code₁
             ∎)))) (
           pc-correct (begin
             pc + codelen code₁ + (if beval b₁ s then 0ℤ else (codelen code₂ + d₀)) +
               codelen code₂ + (if beval b₂ s then d₁ else d₀)
           ≡⟨ cong
               (λ b →
                  pc + codelen code₁ + (if b then _ else _) + codelen code₂ + _)
               eq ⟩
             pc + codelen code₁ + 0ℤ + codelen code₂ + (if beval b₂ s then d₁ else d₀)
           ≡⟨ cong (λ n → n + codelen code₂ + (if beval b₂ s then d₁ else d₀)) (+-identityʳ (pc + codelen code₁)) ⟩
             pc + codelen code₁ + codelen code₂ + (if beval b₂ s then d₁ else d₀)
           ≡⟨ cong (_+ (if beval b₂ s then d₁ else d₀)) (+-assoc pc (codelen code₁) _) ⟩
             pc + (codelen code₁ + codelen code₂) + (if beval b₂ s then d₁ else d₀)
           ≡⟨ cong (λ n → pc + n + (if beval b₂ s then d₁ else d₀)) (sym (codelenApp code₁)) ⟩
             pc + codelen (code₁ ++ code₂) + (if beval b₂ s then d₁ else d₀)
           ∎)))
... | false =
            let code₂ = compile-bexp b₂ d₁ d₀ in
            let code₁ = compile-bexp b₁ 0ℤ (codelen code₂ + d₀) in star-trans (
            compile-bexp-correct b₁ (codeAtAppLeft H)) (
            pc-correct (begin
              pc + codelen code₁ + (if beval b₁ s then 0ℤ else codelen code₂ + d₀)
            ≡⟨ cong (λ b → pc + codelen code₁ + (if b then 0ℤ else codelen code₂ + d₀)) eq ⟩
              pc + codelen code₁ + (codelen code₂ + d₀)
            ≡⟨ sym (+-assoc (pc + codelen code₁) _ _) ⟩
              pc + codelen code₁ + codelen code₂ + d₀
            ≡⟨ cong (λ n → n + d₀) (sym (codelenApp' pc code₁)) ⟩
              pc + codelen (code₁ ++ code₂) + d₀
            ∎))

open import Data.Integer.Tactic.RingSolver

compile-com-correct-terminating : ∀ {s c s'} →
  c / s ⇓ s' →
  ∀ {C pc σ} →
    CodeAt C pc (compile-com c) →
    Transitions C (pc , σ , s) ((pc + codelen (compile-com c)) , σ , s')

compile-com-correct-terminating skip _ =
  pc-correct (sym (+-identityʳ _))

compile-com-correct-terminating (assign x a) {pc = pc} H =
  star-trans (
  compile-aexp-correct a (codeAtAppLeft H)) (one (
  setvar' (codeAtHead (codeAtAppRight _ H)) (codelenApp' pc (compileAExp a))))

compile-com-correct-terminating (seq c₁ c₂ H₁ H₂) {pc = pc} H =
  star-trans (
  compile-com-correct-terminating H₁ (codeAtAppLeft H)) (star-trans (
  compile-com-correct-terminating H₂ (codeAtAppRight _ H)) (
  pc-correct (sym (codelenApp' pc (compile-com c₁)))))

compile-com-correct-terminating {s = s} (ifthenelse b c₁ c₂ {s} Hc) {pc = pc} {σ = σ} H with beval b s | compile-bexp-correct {s = s} b {σ = σ} (codeAtAppLeft H)
... | true | b-correct =
        let code₁ = compile-com c₁ in
        let code₂ = compile-com c₂ in
        let code₀ = compile-bexp b 0ℤ (codelen code₁ + 1ℤ) in star-trans
        b-correct (star-trans (
        pc-correct (+-identityʳ (pc + codelen code₀))) (star-trans (
        compile-com-correct-terminating Hc (codeAtAppRight2 code₀ H)) (one (
        branch {d = codelen code₂} (codeAtHead (codeAtAppRight' code₁ (codeAtAppRight code₀ H) refl))
        (begin
          pc + codelen (code₀ ++ code₁ ++ Ibranch _ ∷ code₂)
        ≡⟨ codelenApp' pc code₀ ⟩
          pc + codelen code₀ + codelen (code₁ ++ Ibranch _ ∷ code₂)
        ≡⟨ codelenApp' (pc + codelen code₀) code₁ ⟩
          pc + codelen code₀ + codelen code₁ + (1ℤ + codelen code₂)
        ≡⟨ sym (+-assoc (pc + codelen code₀ + codelen code₁) 1ℤ (codelen code₂)) ⟩
          pc + codelen code₀ + codelen code₁ + 1ℤ + codelen code₂
        ∎)))))
... | false | b-correct =
        let code₁ = compile-com c₁ in
        let code₂ = compile-com c₂ in
        let code₀ = compile-bexp b 0ℤ (codelen code₁ + 1ℤ) in star-trans
        b-correct (star-trans (
        compile-com-correct-terminating Hc
          (Eq.subst (λ x → CodeAt _ x code₂) (+-assoc (pc + codelen code₀) (codelen code₁) 1ℤ)
          (codeAtTail (codeAtAppRight code₁ (codeAtAppRight code₀ H))))) (
        pc-correct (begin
          pc + codelen code₀ + (codelen code₁ + 1ℤ) + codelen code₂
        ≡⟨ +-assoc (pc + codelen code₀) (codelen code₁ + 1ℤ) (codelen code₂) ⟩
          pc + codelen code₀ + (codelen code₁ + 1ℤ + codelen code₂)
        ≡⟨ cong (_+_ (pc + codelen code₀)) (+-assoc (codelen code₁) 1ℤ (codelen code₂)) ⟩
          pc + codelen code₀ + (codelen code₁ + (1ℤ + codelen code₂))
        ≡⟨ sym (+-assoc (pc + codelen code₀) (codelen code₁) (1ℤ + codelen code₂)) ⟩
          pc + codelen code₀ + codelen code₁ + (1ℤ + codelen code₂)
        ≡⟨ sym (codelenApp' (pc + codelen code₀) code₁) ⟩
          pc + codelen code₀ + codelen (code₁ ++ Ibranch _ ∷ code₂)
        ≡⟨ sym (codelenApp' pc code₀) ⟩
          pc + codelen (code₀ ++ code₁ ++ Ibranch _ ∷ code₂)
        ∎)))

compile-com-correct-terminating (while-done b c Hb) {pc = pc} H =
  let codec = compile-com c in
  let codeb = compile-bexp b 0ℤ (codelen codec + 1ℤ) in
  star-trans (
  compile-bexp-correct b (codeAtAppLeft H)) (star-trans (
  pc-correct (cong (λ b → pc + codelen codeb + (if b then _ else _)) Hb)) (
  pc-correct (trans (+-assoc pc (codelen codeb) _) (begin
    pc + (codelen codeb + (codelen codec + 1ℤ))
  ≡⟨ sym (+-assoc pc (codelen codeb) (codelen codec + 1ℤ)) ⟩
    pc + codelen codeb + (codelen codec + 1ℤ)
  ≡⟨ cong (_+_ (pc + codelen codeb)) (sym (codelenApp codec)) ⟩
    pc + codelen codeb + codelen (codec ++ Ibranch _ ∷ [])
  ≡⟨ sym (codelenApp' pc codeb) ⟩
    pc + codelen (codeb ++ codec ++ Ibranch _ ∷ [])
  ∎))))

compile-com-correct-terminating (while-loop b c Hb Hc Hwhile) {pc = pc} H =
  let codec = compile-com c in
  let codeb = compile-bexp b 0ℤ (codelen codec + 1ℤ) in
  star-trans (
  compile-bexp-correct b (codeAtAppLeft H)) (star-trans (
  pc-correct (cong (λ b → pc + codelen codeb + (if b then _ else _)) Hb)) (star-trans (
  pc-correct (+-identityʳ (pc + codelen codeb))) (star-trans (
  compile-com-correct-terminating Hc (codeAtAppRight2 codeb H)) (star-trans (
  one (branch (codeAtHead (codeAtAppRight codec (codeAtAppRight codeb H))) (simpl pc (codelen codeb) (codelen codec) 1ℤ))) (
  compile-com-correct-terminating Hwhile H))))) where
  simpl : ∀ a b c d → a ≡ a + b + c + d + - (b + c + d)
  simpl = solve-∀
