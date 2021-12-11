/-
Grammaire hors context
Auteur: Alexandre Benguerel
-/

import computability.language

/-
charac : caractère, donc terminal ou variable
a : Type des terminaux
v : Type des variables
-/
inductive charac (a : Type*) (v : Type*)
| term : a → charac
| var : v → charac

/-
La grammaire hors context
Défini par une variable de départ et un ensemble de règle
-/
structure CFG (a : Type*) (v : Type*) :=
(Start : v)
(Rules : set (v → list (charac a v)))

namespace CFG

variables {a : Type*} {v : Type*} (G : CFG a v)

instance charac.has_coe_a : has_coe a (charac a v) := ⟨@charac.term a v⟩
instance : has_coe (list a) (list (charac a v)) := ⟨list.map coe⟩

instance [inhabited v] : inhabited (CFG a v) :=
⟨CFG.mk (default v) ∅⟩

def eval_from : v → list (charac a v) → Prop
| start w :=
∃ r ∈ G.Rules, ∃ a b c, w = a ++ b ++ c ∧ b ≠ [] ∧ by exact r start = b 
∧ eval_from start (a ++ [charac.var start] ++ c)

def eval (w : list (charac a v)) : Prop :=
G.eval_from G.Start w

/-
Probleme, conversion entre `list a` et `list charac`?
-/
def accepts : language a :=
λ x, G.eval x

/-
Encore la meme chose, conversion entre `list a` et `list charac`?
-/
lemma mem_accepts (m : list a) : m ∈ G.accepts ↔ G.eval_from G.Start m := by refl

lemma pumping_lemma :
  ∃ p ≥ 1, ∀ x : list a, x ∈ G.accepts ∧ x.length ≥ p → 
  ∃ a b c d e, x = a ++ b ++ c ++ d ++ e ∧ b ++ d ≠ [] ∧ b.length + c.length + d.length ≤ p ∧ 
  {a} * language.star {b} * {c} * language.star {d} * {e} ≤ G.accepts :=
  sorry

end CFG
