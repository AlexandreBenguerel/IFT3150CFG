/-
Grammaire hors context
Auteur: Alexandre Benguerel

Version pré-présentation: 14 décembre 2021
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

/-
Permet de convertir d'une liste de terminaux vers une liste de caractères
-/
instance charac.has_coe_a : has_coe a (charac a v) := ⟨@charac.term a v⟩
instance : has_coe (list a) (list (charac a v)) := ⟨list.map coe⟩

instance [inhabited v] : inhabited (CFG a v) :=
⟨CFG.mk (default v) ∅⟩

/-
Définition de base du fonctionnement de la grammaire
Problème avec la récurtion. Possible problème avec comment j'essaie de définition cela.
-/
def eval_from : v → list (charac a v) → Prop
| start w :=
∃ r ∈ G.Rules, ∃ a b c, w = a ++ b ++ c ∧ b ≠ [] ∧ by exact r start = b 
∧ eval_from start (a ++ [charac.var start] ++ c)

def eval (w : list (charac a v)) : Prop :=
G.eval_from G.Start w

def accepts : language a :=
λ x, G.eval x

lemma mem_accepts (m : list a) : m ∈ G.accepts ↔ G.eval_from G.Start m := by refl

/-
Lemme principal de la preuve
Énoncé seulement, il reste d'autres choses à corriger avant de passer à cette preuve.
-/
lemma pumping_lemma :
  ∃ p ≥ 1, ∀ x : list a, x ∈ G.accepts ∧ x.length ≥ p → 
  ∃ a b c d e, x = a ++ b ++ c ++ d ++ e ∧ b ++ d ≠ [] ∧ b.length + c.length + d.length ≤ p ∧ 
  {a} * language.star {b} * {c} * language.star {d} * {e} ≤ G.accepts :=
  sorry

end CFG
