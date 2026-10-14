(** * Example programs, and a verified triple of each kind

    The programs are written in the state-and-exceptions monad
    [stdivexcndNE nat].  An outcome from a start state is divergence, a
    raised exception, or a result with its final state.  Each file of
    [TriplesExamples/] holds one example: the program, the set of its
    outcomes ([progA_out] &c.), and the triples proved of it, each read off
    that set.

    One example for each of the sixteen kinds of triple:

                  [Under]                  [Over]
      DWP    [progA_dwp_under]        [progRet_dwp_over]
      DWLP   [progB_dwlp_under]       [progRet_dwlp_over]
      AWP    [progA_awp_under]        [progA_awp_over]
      AWLP   [progB_awlp_under]       [progRet_awlp_over]
      ASP    [progA_asp_under]        [progA_asp_over]
      DSLP   [progEx_dslp_under]      [progA_dslp_over]
      DSP    [progRet_dsp_under]      [progRet_dsp_over]
      ASLP   [progRet_aslp_under]     [progRet_aslp_over]

    A WP [Under] triple says the precondition is included in [wp] of the
    postcondition; an SP [Under] triple says the postcondition is included
    in [sp] of the precondition, which for ASP is an incorrectness triple.

      [ProgA.v]        [progA]: put [42], then keep it or add [1]
      [ProgB.v]        [progB]: put [42], then keep it or diverge
      [ProgRet.v]      [progRet]: [ret tt]
      [ProgEx.v]       [progEx]: add [1], or put [42]
      [Withdrawal.v]   [progloom], [progloom_harder]: "a bug is reachable"
                       from every start state (AWP) or from some (ASP)
      [OHearn.v]       [example_state]: Example 3.1 of O'Hearn's
                       "Incorrectness Logic"
      [ITreePrograms.v] [progA] as an ITree program, through [denoteStExc]
      [Counter.v]      [counter N]: a loop whose bug is reached after many
                       iterations; the incorrectness-logic triples, and
                       incorrectness against Lisbon logic
      [Common.v]       the pre- and postcondition [preEq0], [postEq0] *)

From Incorrectness.Verification.DivNonDetStExc.TriplesExamples Require Export
  Common ProgA ProgB ProgRet ProgEx Withdrawal OHearn ITreePrograms Counter.

