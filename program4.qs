namespace QPNReachability {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Diagnostics;

    operation EncodeCount(place : Qubit[], count : Int) : Unit is Adj + Ctl {
        if ((count &&& 2) != 0) { X(place[0]); }
        if ((count &&& 1) != 0) { X(place[1]); }
    }

    operation ControlledIncrementWithTwoControls(c1 : Qubit, c2 : Qubit, place : Qubit[]) : Unit is Adj + Ctl {
        Controlled X([c1, c2, place[1]], place[0]);
        Controlled X([c1, c2], place[1]);
    }

    operation ControlledDecrementWithTwoControls(c1 : Qubit, c2 : Qubit, place : Qubit[]) : Unit is Adj + Ctl {
        Controlled X([c1, c2], place[1]);
        Controlled X([c1, c2, place[1]], place[0]);
    }

    operation ComputeNonZero(place : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        CNOT(place[0], flag);
        CNOT(place[1], flag);
        CCNOT(place[0], place[1], flag);
    }

    operation ComputeAlpha01(alpha : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        within { X(alpha[0]); }
        apply { CCNOT(alpha[0], alpha[1], flag); }
    }

    operation ComputeAlpha10(alpha : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        within { X(alpha[1]); }
        apply { CCNOT(alpha[0], alpha[1], flag); }
    }

    operation ComputeAlpha11(alpha : Qubit[], flag : Qubit) : Unit is Adj + Ctl {
        CCNOT(alpha[0], alpha[1], flag);
    }

    operation UT(marking : Qubit[], alpha : Qubit[], fired : Qubit) : Unit is Adj + Ctl {

        let p1 = marking[0..1];
        let p2 = marking[2..3];
        let p3 = marking[4..5];
        let p4 = marking[6..7];
        let p5 = marking[8..9];

        use nz = Qubit[3];
        use isT1 = Qubit();
        use isT2 = Qubit();
        use isT3 = Qubit();

        ComputeNonZero(p1, nz[0]);
        ComputeNonZero(p2, nz[1]);
        ComputeNonZero(p3, nz[2]);

        ComputeAlpha01(alpha, isT1);
        ComputeAlpha10(alpha, isT2);
        ComputeAlpha11(alpha, isT3);

        // fired = 1 iff selected transition is enabled
        Controlled X([isT1, nz[0], nz[1]], fired);
        Controlled X([isT2, nz[2]], fired);
        Controlled X([isT3, nz[2]], fired);

        // uncompute temporary flags before changing the marking
        ComputeAlpha11(alpha, isT3);
        ComputeAlpha10(alpha, isT2);
        ComputeAlpha01(alpha, isT1);

        ComputeNonZero(p3, nz[2]);
        ComputeNonZero(p2, nz[1]);
        ComputeNonZero(p1, nz[0]);

        // decode alpha again
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

        ComputeAlpha11(alpha, isT3);
        ComputeAlpha10(alpha, isT2);
        ComputeAlpha01(alpha, isT1);
    }

    operation PhaseI(
        marking : Qubit[],
        alpha1 : Qubit[],
        alpha2 : Qubit[],
        alpha3 : Qubit[],
        fired1 : Qubit,
        fired2 : Qubit,
        fired3 : Qubit
    ) : Unit is Adj + Ctl {

        let p1 = marking[0..1];
        let p2 = marking[2..3];
        let p3 = marking[4..5];
        let p4 = marking[6..7];
        let p5 = marking[8..9];

        EncodeCount(p1, 2);
        EncodeCount(p2, 1);
        EncodeCount(p3, 0);
        EncodeCount(p4, 0);
        EncodeCount(p5, 0);

        H(alpha1[0]);
        H(alpha1[1]);
        UT(marking, alpha1, fired1);

        H(alpha2[0]);
        H(alpha2[1]);
        UT(marking, alpha2, fired2);

        H(alpha3[0]);
        H(alpha3[1]);
        UT(marking, alpha3, fired3);
    }

    operation OracleTargetMarking(marking : Qubit[], target : Int) : Unit is Adj + Ctl {
        let weights = [512, 256, 128, 64, 32, 16, 8, 4, 2, 1];

        within {
            for i in 0..9 {
                if ((target &&& weights[i]) == 0) {
                    X(marking[i]);
                }
            }
        } apply {
            H(marking[9]);
            Controlled X(marking[0..8], marking[9]);
            H(marking[9]);
        }
    }

    operation ReflectionAboutZero(register : Qubit[]) : Unit is Adj + Ctl {
        let n = Length(register);

        within {
            for q in register {
                X(q);
            }
        } apply {
            H(register[n - 1]);
            Controlled X(register[0..n - 2], register[n - 1]);
            H(register[n - 1]);
        }
    }

    operation GroverIteration(
        marking : Qubit[],
        alpha1 : Qubit[],
        alpha2 : Qubit[],
        alpha3 : Qubit[],
        fired1 : Qubit,
        fired2 : Qubit,
        fired3 : Qubit,
        target : Int
    ) : Unit {

        let allRegs =
            marking
            + alpha1 + [fired1]
            + alpha2 + [fired2]
            + alpha3 + [fired3];

        OracleTargetMarking(marking, target);

        Adjoint PhaseI(
            marking,
            alpha1,
            alpha2,
            alpha3,
            fired1,
            fired2,
            fired3
        );

        ReflectionAboutZero(allRegs);

        PhaseI(
            marking,
            alpha1,
            alpha2,
            alpha3,
            fired1,
            fired2,
            fired3
        );
    }

    operation MeasureMarkingAsInt(marking : Qubit[]) : Int {
        mutable value = 0;
        let weights = [512, 256, 128, 64, 32, 16, 8, 4, 2, 1];

        for i in 0..9 {
            if (M(marking[i]) == One) {
                set value += weights[i];
            }
        }

        return value;
    }

    @EntryPoint()
    operation Main() : Unit {

        // Choose target marking here.
        //
        // 1001000000 = (2,1,0,0,0), decimal 576
        // 0100100000 = (1,0,2,0,0), decimal 288
        // 0100010100 = (1,0,1,1,0), decimal 276
        // 0100010001 = (1,0,1,0,1), decimal 273
        // 0100001000 = (1,0,0,2,0), decimal 264
        // 0100000101 = (1,0,0,1,1), decimal 261
        // 0100000010 = (1,0,0,0,2), decimal 258

        let target = 288;
        let groverIterations = 1;

        mutable count1001000000 = 0;
        mutable count0100100000 = 0;
        mutable count0100010100 = 0;
        mutable count0100010001 = 0;
        mutable count0100001000 = 0;
        mutable count0100000101 = 0;
        mutable count0100000010 = 0;
        mutable other = 0;

        for shot in 1..100 {

            use marking = Qubit[10];

            use alpha1 = Qubit[2];
            use alpha2 = Qubit[2];
            use alpha3 = Qubit[2];

            use fired1 = Qubit();
            use fired2 = Qubit();
            use fired3 = Qubit();

            let allRegs =
                marking
                + alpha1 + [fired1]
                + alpha2 + [fired2]
                + alpha3 + [fired3];

            PhaseI(
                marking,
                alpha1,
                alpha2,
                alpha3,
                fired1,
                fired2,
                fired3
            );

            for _ in 1..groverIterations {
                GroverIteration(
                    marking,
                    alpha1,
                    alpha2,
                    alpha3,
                    fired1,
                    fired2,
                    fired3,
                    target
                );
            }

            let measured = MeasureMarkingAsInt(marking);

            if (measured == 576) {
                set count1001000000 += 1;
            } elif (measured == 288) {
                set count0100100000 += 1;
            } elif (measured == 276) {
                set count0100010100 += 1;
            } elif (measured == 273) {
                set count0100010001 += 1;
            } elif (measured == 264) {
                set count0100001000 += 1;
            } elif (measured == 261) {
                set count0100000101 += 1;
            } elif (measured == 258) {
                set count0100000010 += 1;
            } else {
                set other += 1;
            }

            ResetAll(allRegs);
        }

        Message($"Grover iterations: {groverIterations}");
        Message($"Target decimal value: {target}");
        Message("Results after 100 shots:");
        Message($"1001000000 = (2,1,0,0,0), decimal 576: {count1001000000}");
        Message($"0100100000 = (1,0,2,0,0), decimal 288: {count0100100000}");
        Message($"0100010100 = (1,0,1,1,0), decimal 276: {count0100010100}");
        Message($"0100010001 = (1,0,1,0,1), decimal 273: {count0100010001}");
        Message($"0100001000 = (1,0,0,2,0), decimal 264: {count0100001000}");
        Message($"0100000101 = (1,0,0,1,1), decimal 261: {count0100000101}");
        Message($"0100000010 = (1,0,0,0,2), decimal 258: {count0100000010}");
        Message($"Other: {other}");
    }
}