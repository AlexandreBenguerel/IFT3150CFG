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

instance [inhabited v] : inhabited (CFG a v) :=
⟨CFG.mk (default v) ∅⟩

def eval_from (start : v) (w : list (charac a v)) : Prop :=
∃ r ∈ G.Rules, ∃ a b c, w = a ++ b ++ c ∧ r start = b /- ∧ Reste une derniere condition apres-/

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

lemma pumping_lemma {x : list a} (hx : x ∈ G.accepts) :
  ∃ p ≥ 1, x.length ≥ p → 
  ∃ a b c d e, x = a ++ b ++ c ++ d ++ e ∧ b ++ d ≠ [] ∧ b.length + c.length + d.length ≤ p ∧ 
  {a} * language.star {b} * {c} * language.star {d} * {e} ≤ G.accepts :=
  sorry

end CFG
