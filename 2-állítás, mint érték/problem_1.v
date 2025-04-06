(* 
  Lemma: Ha A és (B vagy C) igaz, akkor következik, hogy 
  (A és B) vagy (A és C) igaz.

  Ez a logikai disztributivitás egyik alapesete:
  A ∧ (B ∨ C) ⟹ (A ∧ B) ∨ (A ∧ C)
*)

Lemma problem_1 : forall A B C : Prop, A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
  (* Bevezetjük az állítás összes szereplőjét és feltételét *)
  intros A B C [HA HBC].

  (* Most külön-külön vizsgáljuk meg, hogy B vagy C igaz-e *)
  destruct HBC as [HB | HC].

  - (* Első eset: B igaz *)
    left.                (* azt fogjuk bizonyítani, hogy A /\ B igaz *)
    split. exact HA. exact HB.

  - (* Második eset: C igaz *)
    right.               (* azt fogjuk bizonyítani, hogy A /\ C igaz *)
    split. exact HA. exact HC.

Qed.
