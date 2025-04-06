(* 
  Lemma: Ha B -> A és C -> A, akkor B \/ C -> A 
  Vagyis ha A következik B-ből és C-ből is, akkor ha B vagy C igaz, A következik.
*)

Lemma problem_2 : forall A B C : Prop, ((B -> A) /\ (C -> A)) -> (B \/ C -> A).
Proof.
  (* Bevezetjük az állítás összes részét: A, B, C és a feltételt *)
  intros A B C [HBA HCA].

  (* Most vizsgáljuk meg a B \/ C diszjunkciót *)
  intros [HB | HC].

  - (* Első eset: B igaz *)
    apply HBA.    (* alkalmazzuk a B -> A implikációt *)
    assumption.   (* B adott, tehát A következik *)

  - (* Második eset: C igaz *)
    apply HCA.    (* alkalmazzuk a C -> A implikációt *)
    assumption.   (* C adott, tehát A következik *)

Qed.
