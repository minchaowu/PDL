import data.list
open list nat

namespace PDL

inductive pdl_type
| Fml | Prg

open pdl_type

attribute [reducible]
def PropVar := nat

attribute [reducible]
def ProgVar := nat

inductive pdl : pdl_type → Type
| Var (n : PropVar)                 : pdl Fml
| Neg (φ : pdl Fml)                 : pdl Fml
| And (φ : pdl Fml) (ψ : pdl Fml)   : pdl Fml
| Or  (φ : pdl Fml) (ψ : pdl Fml)   : pdl Fml
| EF (a : pdl Prg) (φ : pdl Fml)    : pdl Fml
| AX (a : pdl Prg) (φ : pdl Fml)    : pdl Fml
| Atom (n : ProgVar)                : pdl Prg
| Test (φ : pdl Fml)                : pdl Prg
| Cons (a : pdl Prg) (b : pdl Prg)  : pdl Prg
| Nd (a : pdl Prg) (b : pdl Prg)    : pdl Prg
| Star (a : pdl Prg)                : pdl Prg 

open pdl

notation `#`:max P:max := Var P
notation A ∨ B         := Or A B
notation A ∧ B         := And A B
notation ~ A           := Neg A
notation `⟨` a `⟩` φ      := EF a φ 
notation `[` a `]` φ      := AX a φ 
notation φ `??`        := Test φ
notation a `;` b      := Cons a b
notation a `∪` b     := Nd a b
notation a `⋆`        := Star a

notation A ` ⇒ ` B     := Neg A ∨ B
def BiImpl A B  := A ⇒ B ∧ B ⇒ A
infixr `⇔`:27 := BiImpl

section

-- Using these definitions and notations, we can express formulae of PDL 
-- naturally.

variables (φ ψ p: pdl Fml) (a b: pdl Prg)

check [a](φ ⇒ ψ) ⇒ ([a]φ ⇒ [a]ψ)
check [(a;b)]φ ⇔ [a][b]φ
check [a⋆]φ ⇔ φ ∧ [a][a⋆]φ
check [φ??]ψ ⇔ (φ ⇒ ψ)

-- Induction principle
check φ ∧ [a⋆](φ ⇒ [a]φ) ⇒ [a⋆]φ 

-- Some eventualities and other examples
check ⟨a⟩⟨a⋆⟩[a]p
check ⟨b⟩⟨b⋆⟩⟨(a⋆;b⋆)⋆⟩p
check [(a∪b)⋆]~p

end

-- A simpler definition of Kripke structures for PDL.
structure kripke :=
(prop_eval : ℕ → PropVar → Prop)
(prog_eval : ProgVar → ℕ → ℕ → Prop)

-- This is a more general definition of kripke structures.

-- structure kripke :=
-- (world : Type)
-- (prop_eval : world → PropVar → bool)
-- (prog_eval : ProgVar → world → world → bool)

section
-- This says only propositions 0,1,2,3 are true in every world.
private def f (w : ℕ) (p : PropVar) : Prop := if p > 4 then false else true
-- This says worlds 0,1,2,3 are fully connected via atomic program 2. No other
-- worlds are connected together.
private def g (a : ProgVar) (w₁ w₂: ℕ) : Prop := 
if a = 2 ∧ w₁ ≤ 3 ∧ w₂ ≤ 3 then true else false
-- Now we have a kripke structure where worlds 0,1,2,3 are are fully connected 
-- via atomic program 2, and propostions 0,1,2,3 are true in these worlds. 
private def my_model : kripke := kripke.mk f g 

end 

section ith

variable {T : Type}
definition ith : Π (l : list T) (i : nat), i < length l → T
| nil     i        h := absurd h (not_lt_zero i)
| (x::xs) 0        h := x
| (x::xs) (succ i) h := ith xs i (lt_of_succ_lt_succ h)

end ith

-- The following defs require well-founded recursion and mutually recursive 
-- definition which have not been implemented in Lean 3 yet. To handle the
-- mutual definition, we simply cheat by making the semantics of Test 
-- unrelatd to prog_eval. To handle well-founded recursion, we can mark 
-- these as meta definitions.

def Acc (M : kripke) : ℕ → ℕ → pdl Prg → Prop
| w₁ w₂ (Atom n)      := kripke.prog_eval M n w₁ w₂
| w₁ w₂ (Test φ)      := false
| w₁ w₂ (Cons γ δ)    := ∃ y, Acc w₁ y γ ∧ Acc y w₂ δ 
| w₁ w₂ (Nd γ δ)      := Acc w₁ w₂ γ ∨ Acc w₁ w₂ δ
| w₁ w₂ (Star γ)      := ∃ n : ℕ, ∃ l : list ℕ, length l = n ∧ 
                         head l = w₁ ∧ head (reverse l) = w₂ ∧ 
                         ∀i, i + 1 < length l → 
                         Acc (ith l i begin apply lt_of_succ_lt a end) 
                         (ith l (i+1) begin exact a end) γ

def Satisfies (M : kripke) : ℕ → pdl Fml → Prop 
| w (# P)         := kripke.prop_eval M w P 
| w (~ φ)         := ¬ (Satisfies w φ)
| w (And φ ψ)     := Satisfies w φ ∧ Satisfies w ψ
| w (Or φ ψ)      := Satisfies w φ ∨ Satisfies w ψ
| w (EF a φ)      := ∃ y, Acc M w y a ∧ Satisfies y φ
| w (AX a φ)      := ∀ y, Acc M w y a → Satisfies y φ

-- Satisfiability 

notation M ` & ` w ` ⊨ ` p := Satisfies M w p

def Satisfiable (φ : pdl Fml) : Prop := ∃ M w, M & w ⊨ φ

def Valid (φ : pdl Fml) : Prop := ∀ M w, M & w ⊨ φ

end PDL

-- Some experiments.

-- constant Kripke_model : Type
-- constant valuation : Kripke_model → Type

-- constant semantic_type : Kripke_model → pdl_type → Type 

-- open pdl

-- noncomputable def semantics (K : Kripke_model) (v : valuation K) : 
--   Π t : pdl_type, Π e : pdl t, semantic_type K t
-- | ._  (var  n)    := sorry
-- | ._  (fneg φ)    := sorry
-- | ._  (event γ φ) := sorry

-- mutual inductive pdlfml, pdlprg
-- with pdlfml : Type
-- | var (n : ℕ) : pdlfml
-- | event (γ : pdlprg) (φ : pdlfml) : pdlfml
-- with pdlprg : Type
-- | atom (n : ℕ) : pdlprg

-- inductive tree : Type 
-- | mk : list tree → tree

-- print _nest_1_1.tree

-- print pdlfml
-- print pdlfml._mut_

-- def fake (n : ℕ) : Prop := if n < 4 then true else false

-- check @if_pos

-- theorem thm : fake 0 := trivial

-- example : true := by trivial
