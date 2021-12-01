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

/-
Je sais pas si j'ai besoin de ça, il y avait ça dans le fichier DFA.
-/
instance [inhabited v] : inhabited (CFG a v) :=
⟨CFG.mk (default v) ∅⟩

end CFG
