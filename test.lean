import Mathlib

lemma test_get_map {α β : Type} (f : α → β) (l : List α) (i : Fin (l.map f).length) (i' : Fin l.length) (h : i.val = i'.val) :
  (l.map f).get i = f (l.get i') := by
  have h1 : (l.map f).get i = (l.map f)[i.val] := rfl
  have h2 : l.get i' = l[i'.val] := rfl
  rw [h1, h2, h]
  exact List.getElem_map f l i'.val i'.isLt
