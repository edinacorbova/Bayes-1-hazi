(* 
  Lemma: Ha A vagy ~A igaz, és ha A -> B implikációból A következik, 
  akkor A igaz.
*)

Lemma problem_3 : forall A B : Prop, (A \/ ~A) -> ((A -> B) -> A) -> A.
Proof.
  (* Bevezetjük az összes állítást *)
  intros A B H H1.

  (* Eseteket vizsgálunk A \/ ~A alapján *)
  destruct H as [HA | HnA].

  - (* Első eset: A igaz *)
    exact HA.  (* ez a cél, meg is van *)

  - (* Második eset: nem A igaz *)
    (* Feltételezzük, hogy A -> B *)
    apply H1.  
    (* A cél most: A -> B *)
    intro A_ell.  
    (* De ha A igaz lenne, az ellentmond a feltételnek (~A) *)
    contradiction.
Qed.
