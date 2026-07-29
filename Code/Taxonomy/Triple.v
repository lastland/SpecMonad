(** * Shared triple approximation direction.

    [approximationKind] distinguishes under- vs over-approximation in
    both WP ([tripleWP]) and SP ([tripleSP]) triples. *)

Inductive approximationKind := | Under | Over.
