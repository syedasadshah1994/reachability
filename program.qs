namespace QPNReachability {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Diagnostics;

    operation EncodeCount(place : Qubit[], count : Int) : Unit {
        if ((count &&& 2) != 0) { X(place[0]); }
        if ((count &&& 1) != 0) { X(place[1]); }
    }

    operation ControlledIncrementWithTwoControls(c1 : Qubit, c2 : Qubit, place : Qubit[]) : Unit {
        Controlled X([c1, c2, place[1]], place[0]);
        Controlled X([c1, c2], place[1]);
    }

    operation ControlledDecrementWithTwoControls(c1 : Qubit, c2 : Qubit, place : Qubit[]) : Unit {
        Controlled X([c1, c2], place[1]);
        Controlled X([c1, c2, place[1]], place[0]);
    }

    operation ComputeNonZero(place : Qubit[], flag : Qubit) : Unit {
        CNOT(place[0], flag);
        CNOT(place[1], flag);
        CCNOT(place[0], place[1], flag);
    }

    operation ComputeAlpha01(alpha : Qubit[], flag : Qubit) : Unit {
        within { X(alpha[0]); }
        apply { CCNOT(alpha[0], alpha[1], flag); }
    }

    operation ComputeAlpha10(alpha : Qubit[], flag : Qubit) : Unit {
        within { X(alpha[1]); }
        apply { CCNOT(alpha[0], alpha[1], flag); }
    }

    operation ComputeAlpha11(alpha : Qubit[], flag : Qubit) : Unit {
        CCNOT(alpha[0], alpha[1], flag);
    }

    operation UT(marking : Qubit[], alpha : Qubit[], fired : Qubit) : Unit {

        let p1 = marking[0..1];
        let p2 = marking[2..3];
        let p3 = marking[4..5];
        let p4 = marking[6..7];
        let p5 = marking[8..9];

        use nz = Qubit[3];
        use isT1 = Qubit();
        use isT2 = Qubit();
        use isT3 = Qubit();

        // compute nonzero flags from OLD marking
        ComputeNonZero(p1, nz[0]);
        ComputeNonZero(p2, nz[1]);
        ComputeNonZero(p3, nz[2]);

        // decode alpha
        ComputeAlpha01(alpha, isT1); // alpha = 01 means T1
        ComputeAlpha10(alpha, isT2); // alpha = 10 means T2
        ComputeAlpha11(alpha, isT3); // alpha = 11 means T3

        // fired = 1 iff selected transition is enabled
        Controlled X([isT1, nz[0], nz[1]], fired);
        Controlled X([isT2, nz[2]], fired);
        Controlled X([isT3, nz[2]], fired);

        // uncompute temporary flags before marking changes
        ComputeAlpha11(alpha, isT3);
        ComputeAlpha10(alpha, isT2);
        ComputeAlpha01(alpha, isT1);

        ComputeNonZero(p3, nz[2]);
        ComputeNonZero(p2, nz[1]);
        ComputeNonZero(p1, nz[0]);

        // decode alpha again; now alpha + fired tells which transition fired
        ComputeAlpha01(alpha, isT1);
        ComputeAlpha10(alpha, isT2);
        ComputeAlpha11(alpha, isT3);

        // T1: P1 + P2 -> 2P3
        ControlledDecrementWithTwoControls(fired, isT1, p1);
        ControlledDecrementWithTwoControls(fired, isT1, p2);
        ControlledIncrementWithTwoControls(fired, isT1, p3);
        ControlledIncrementWithTwoControls(fired, isT1, p3);

        // T2: P3 -> P4
        ControlledDecrementWithTwoControls(fired, isT2, p3);
        ControlledIncrementWithTwoControls(fired, isT2, p4);

        // T3: P3 -> P5
        ControlledDecrementWithTwoControls(fired, isT3, p3);
        ControlledIncrementWithTwoControls(fired, isT3, p5);

        // uncompute alpha decoder
        ComputeAlpha11(alpha, isT3);
        ComputeAlpha10(alpha, isT2);
        ComputeAlpha01(alpha, isT1);
    }

    @EntryPoint()
    operation Main() : Unit {

        use marking = Qubit[10];

        let p1 = marking[0..1];
        let p2 = marking[2..3];
        let p3 = marking[4..5];
        let p4 = marking[6..7];
        let p5 = marking[8..9];

        use alpha1 = Qubit[2];
        use alpha2 = Qubit[2];
        use alpha3 = Qubit[2];

        use fired1 = Qubit();
        use fired2 = Qubit();
        use fired3 = Qubit();

        EncodeCount(p1, 2);
        EncodeCount(p2, 1);
        EncodeCount(p3, 0);
        EncodeCount(p4, 0);
        EncodeCount(p5, 0);

        Message("Initial marking:");
        Message("Expected marking bits: 1001000000");
        DumpRegister(marking);

        H(alpha1[0]);
        H(alpha1[1]);

        Message("After superposing alpha1:");
        Message("Register order: marking + alpha1");
        DumpRegister(marking + alpha1);

        UT(marking, alpha1, fired1);

        Message("After first iteration:");
        Message("Register order: marking + alpha1 + fired1");
        DumpRegister(marking + alpha1 + [fired1]);

        H(alpha2[0]);
        H(alpha2[1]);

        Message("After superposing alpha2:");
        Message("Register order: marking + alpha1 + fired1 + alpha2");
        DumpRegister(marking + alpha1 + [fired1] + alpha2);

        UT(marking, alpha2, fired2);

        Message("After second iteration:");
        Message("Register order: marking + alpha1 + fired1 + alpha2 + fired2");
        DumpRegister(marking + alpha1 + [fired1] + alpha2 + [fired2]);

        H(alpha3[0]);
        H(alpha3[1]);

        Message("After superposing alpha3:");
        Message("Register order: marking + alpha1 + fired1 + alpha2 + fired2 + alpha3");
        DumpRegister(marking + alpha1 + [fired1] + alpha2 + [fired2] + alpha3);

        UT(marking, alpha3, fired3);

        Message("After third iteration:");
        Message("Register order: marking + alpha1 + fired1 + alpha2 + fired2 + alpha3 + fired3");
        DumpRegister(marking + alpha1 + [fired1] + alpha2 + [fired2] + alpha3 + [fired3]);

        ResetAll(
            marking
            + alpha1 + alpha2 + alpha3
            + [fired1] + [fired2] + [fired3]
        );
    }
}