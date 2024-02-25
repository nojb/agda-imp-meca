open import IMP
open import Data.List as List
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Bool using (true; false; not; Bool; if_then_else_; T)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Data.Nat
import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Properties using (length-++; ++-assoc)
open import Data.Integer.Properties using (+-assoc; suc-pred; pred-suc; suc-+; +-identityʳ)
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
codelen C = + (List.length C)

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

add' : ∀ {C pc σ s n₁ n₂ pc' σ' σ''} →
  InstrAt C pc Iadd →
  pc' ≡ pc + 1ℤ →
  σ'  ≡ n₂ ∷ n₁ ∷ σ →
  σ'' ≡ (n₁ + n₂) ∷ σ →
  Transition C (pc , σ' , s) (pc' , σ'' , s)
add' H Hpc Hσ Hσ' rewrite Hpc rewrite Hσ rewrite Hσ' = add H

opp' : ∀ {C pc σ s n pc' σ₁ σ₂} →
  InstrAt C pc Iopp →
  pc' ≡ pc + 1ℤ →
  σ₁  ≡ n ∷ σ →
  σ₂  ≡ (- n) ∷ σ →
  Transition C (pc , σ₁ , s) (pc' , σ₂ , s)
opp' H Hpc Hσ₁ Hσ₂ rewrite Hpc rewrite Hσ₁ rewrite Hσ₂ = opp H

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
      ≡⟨ cong (_+ codelen C₁) Hpc ⟩
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

compile-aexp-correct : ∀ {C} {s} a {pc} {σ} →
  CodeAt C pc (compileAExp a) →
  Transitions C (pc , σ , s) ((pc + codelen (compileAExp a)) , aeval a s ∷ σ , s)

compile-aexp-correct (CONST _) H = one (const (codeAtHead H))

compile-aexp-correct (VAR _) H = one (var (codeAtHead H))

compile-aexp-correct {_} {_} (PLUS a₁ a₂) {pc} H =
  let C₁ = compileAExp a₁ in
  let C₂ = compileAExp a₂ in
  star-trans (compile-aexp-correct a₁ (codeAtAppLeft H))
    (star-trans (compile-aexp-correct a₂ (codeAtAppRight2 C₁ H))
      (one (add'
        (codeAtHead (codeAtAppRight C₂ (codeAtAppRight C₁ H)))
        (begin
            pc + codelen (C₁ ++ C₂ ++ _)
          ≡⟨ codelenApp pc C₁ ⟩
            pc + codelen C₁ + codelen (C₂ ++ _)
          ≡⟨ codelenApp (pc + codelen C₁) C₂ ⟩
            pc + codelen C₁ + codelen C₂ + 1ℤ
          ∎) refl refl)))

compile-aexp-correct {_} {_} (MINUS a₁ a₂) {pc} H =
  let C₁ = compileAExp a₁ in
  let C₂ = compileAExp a₂ in
  star-trans (compile-aexp-correct a₁ (codeAtAppLeft H))
    (star-trans (compile-aexp-correct a₂ (codeAtAppLeft (codeAtAppRight C₁ H)))
      (star-trans
        (one (opp' (codeAtHead (codeAtAppRight C₂ (codeAtAppRight C₁ H))) refl refl refl))
        (one (add'
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

compile-bexp : BExp → ℤ → ℤ → Code
compile-bexp TRUE d₁ _ = if does (d₁ ≟ 0ℤ) then [] else [ Ibranch d₁ ]
compile-bexp FALSE _ d₀ = if does (d₀ ≟ 0ℤ) then [] else [ Ibranch d₀ ]
compile-bexp (EQUAL a₁ a₂) d₁ d₀ = compileAExp a₁ ++ compileAExp a₂ ++ [ Ibeq d₁ d₀ ]
compile-bexp (LESSEQUAL a₁ a₂) d₁ d₀ = compileAExp a₁ ++ compileAExp a₂ ++ [ Ible d₁ d₀ ]
compile-bexp (NOT b₁) d₁ d₀ = compile-bexp b₁ d₀ d₁
compile-bexp (AND b₁ b₂) d₁ d₀ =
  let C₂ = compile-bexp b₂ d₁ d₀ in
  let C₁ = compile-bexp b₁ 0ℤ (codelen C₂ + d₀) in
  C₁ ++ C₂

if-not : ∀ {a} {A : Set} {b c : A} → (if not a then b else c) ≡ (if a then c else b)
if-not {false} = refl
if-not {true}  = refl

postulate
  compile-bexp-correct : ∀ {C s} b {d₁ d₀ pc σ} →
    CodeAt C pc (compile-bexp b d₁ d₀) →
    Transitions C
      (pc , σ , s)
      ((pc + codelen (compile-bexp b d₁ d₀) + (if beval b s then d₁ else d₀)) , σ , s)

-- compile-bexp-correct {_} {_} TRUE {d₁} {_} {pc} H with d₁ ≟ 0ℤ | Eq.inspect (λ d → d ≟ 0ℤ) d₁
-- ...  | yes p | eq = {!!}
-- ...  | no _  | _                               = one (branch (codeAtHead H) refl)

-- compile-bexp-correct {_} {s} FALSE {_} {d₀} {pc} H with d₀ ≟ 0ℤ
-- ... | yes p with p
-- ... | _ = {!!}
-- compile-bexp-correct {_} {s} FALSE {_} {d₀} {pc} H | no _  = one (branch (codeAtHead H) refl)

-- compile-bexp-correct {_} {s} (EQUAL a₁ a₂) H = {!!}

-- compile-bexp-correct {_} {s} (LESSEQUAL a₁ a₂) H = {!!}

-- compile-bexp-correct {_} {s} (NOT b₁) H with if-not {a = beval b₁ s}
-- ... | _ = star-trans (compile-bexp-correct b₁ H) {!!}

-- compile-bexp-correct {_} {s} (AND b₁ b₂) H = {!!}

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

compile-com-correct-terminating : ∀ {s c s'} →
  c / s ⇓ s' →
  ∀ {C pc σ} →
    CodeAt C pc (compile-com c) →
    Transitions C (pc , σ , s) ((pc + codelen (compile-com c)) , σ , s')

compile-com-correct-terminating skip _ =
  eps' (cong (_, _ , _) (sym (+-identityʳ _)))

compile-com-correct-terminating (assign x a) {_} {pc} H =
  star-trans (compile-aexp-correct a (codeAtAppLeft H))
    (one (setvar' (codeAtHead (codeAtAppRight _ H)) (codelenApp pc (compileAExp a))))

compile-com-correct-terminating (seq c₁ c₂ H₁ H₂) {_} {pc} H =
  star-trans (compile-com-correct-terminating H₁ (codeAtAppLeft H))
    (star-trans (compile-com-correct-terminating H₂ (codeAtAppRight _ H))
      (eps' (cong (_, _ , _) (sym (codelenApp pc (compile-com c₁))))))

compile-com-correct-terminating (ifthenelse b c₁ c₂ Hc) H =
  star-trans (compile-bexp-correct b (codeAtAppLeft H))
    (star-trans (compile-com-correct-terminating Hc {!!}) {!!})

compile-com-correct-terminating (while-done b c Hb) H = {!!}

compile-com-correct-terminating (while-loop b c s Hb Hc) H = {!!}
