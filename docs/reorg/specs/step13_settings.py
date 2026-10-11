V = "Verification"
SOURCES = [f"{V}/Computation/DivNonDetNE.v", f"{V}/MonadMorphisms/MonadMorphisms.v",
           f"{V}/Triples/Triple.v", f"{V}/Triples/MorphismTriples.v", f"{V}/Triples/TripleTaxonomy.v",
           f"{V}/Triples/Examples.v", f"{V}/Triples/InCorrectnessPrinciples.v",
           f"{V}/DijkstraMonads/DijkstraMonad.v", f"{V}/TriplesAsTypings/TriplesAsTypings.v",
           f"{V}/TriplesAsTypings/DijkstraExamples.v"]
G, B, S, E = f"{V}/Generic", f"{V}/Base", f"{V}/State", f"{V}/StateExc"
_m = {
    "DivNonDetNE":   (f"{B}/DivNonDetNE.v", f"{B}/DivNonDetNE.v", f"{S}/ComputationSt.v", f"{E}/ComputationStExc.v"),
    "MonadMorphisms": (f"{B}/MorphismsPure.v", f"{B}/MorphismsPure.v", f"{S}/MorphismsSt.v", f"{E}/MorphismsStExc.v"),
    "Triple":        (f"{G}/Triple.v", f"{B}/TriplesPure.v", f"{S}/TriplesSt.v", f"{E}/TriplesStExc.v"),
    "MorphismTriples": (f"{G}/Triple.v", f"{B}/TriplesPure.v", f"{S}/TriplesSt.v", f"{E}/TriplesStExc.v"),
    "TripleTaxonomy": (f"{G}/TripleTaxonomy.v", f"{B}/TripleTaxonomyPure.v", f"{S}/TripleTaxonomySt.v", f"{E}/TripleTaxonomyStExc.v"),
    "Examples":      (None, None, None, f"{E}/Examples.v"),
    "InCorrectnessPrinciples": (None, None, f"{S}/InCorrectnessPrinciples.v", None),
    "DijkstraMonad": (f"{G}/DijkstraMonad.v", f"{B}/DijkstraPure.v", f"{S}/DijkstraSt.v", f"{E}/DijkstraStExc.v"),
    "TriplesAsTypings": (f"{G}/Typings.v", f"{B}/TypingsPure.v", f"{S}/TypingsSt.v", f"{E}/TypingsStExc.v"),
    "DijkstraExamples": (None, f"{B}/TypingsPure.v", None, f"{E}/DijkstraExamples.v"),
}
TARGET = {}
for src in SOURCES:
    stem = src.rsplit("/", 1)[1][:-2]
    for lv, t in zip(["Generic", "Base", "State", "StateExc"], _m[stem]):
        TARGET[(src, lv)] = t
OVERRIDE = {f"{V}/Triples/Examples.v": "StateExc",
            f"{V}/Triples/InCorrectnessPrinciples.v": "State"}
ORDER = [f"{G}/Triple.v", f"{G}/DijkstraMonad.v", f"{G}/TripleTaxonomy.v", f"{G}/Typings.v",
         f"{B}/DivNonDetNE.v", f"{B}/MorphismsPure.v", f"{B}/TriplesPure.v", f"{B}/TripleTaxonomyPure.v",
         f"{B}/DijkstraPure.v", f"{B}/TypingsPure.v",
         f"{S}/ComputationSt.v", f"{S}/MorphismsSt.v", f"{S}/TriplesSt.v", f"{S}/TripleTaxonomySt.v",
         f"{S}/InCorrectnessPrinciples.v", f"{S}/DijkstraSt.v", f"{S}/TypingsSt.v",
         f"{E}/ComputationStExc.v", f"{E}/MorphismsStExc.v", f"{E}/TriplesStExc.v", f"{E}/TripleTaxonomyStExc.v",
         f"{E}/Examples.v", f"{E}/DijkstraStExc.v", f"{E}/TypingsStExc.v", f"{E}/DijkstraExamples.v"]
HEADER = {t: f"(** * {t.split('/')[1]} setting: {t.rsplit('/',1)[1][:-2]} *)" for t in ORDER}
