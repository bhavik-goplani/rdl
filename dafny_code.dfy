datatype State = Initial | Error | Done

datatype Variables = Variables(
  read:nat,
  write:nat,
  success:nat,
  state:State
)

predicate Init(v:Variables)
{
  && v.state == Initial
  && v.read > 0
  && v.write > 0
  && (v.write > v.read ==> v.write - v.read <= 1)
  && v.success == 0
}

predicate TransitionFromInitialToError (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Initial
  && v'.state == Error
  && v'.read == v.read
  && v'.write == v.write - 1
  && v'.success == v.success == 0
  && (v.write > v.read ==> v.write - v.read <= 1)
}

predicate TransitionFromErrorToError (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Error
  && v'.state == Error
  && v'.read == v.read - 1
  && v'.write == v.write
  && v'.success == v.success == 0
  && (v.write > v.read ==> v.write - v.read <= 1)
}

predicate TransitionFromErrorToInitial (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Error
  && v'.state == Initial
  && v'.read == v.read - 1
  && v'.write == v.write
  && v'.success == v.success == 0
  && (v.write > v.read ==> v.write - v.read <= 1)
}

predicate TransitionFromErrorToDone (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Error
  && v'.state == Done
  && v'.read == v.read - 1
  && v'.write == v.write
  && v'.success == v.success + 1
  && v'.success <= 1
  && (v.write > v.read ==> v.write - v.read <= 1)
}

predicate TransitionFromInitialToDone (v:Variables, v':Variables)
  requires Valid(v)
{
  && v.state == Initial
  && v'.state == Done
  && v'.read == v.read
  && v'.write == v.write - 1
  && v'.success == v.success + 1
  && v'.success <= 1
  && (v.write > v.read ==> v.write - v.read <= 1)
}

datatype Step = 
  | TransitionFromInitialToErrorStep()
  | TransitionFromErrorToErrorStep()
  | TransitionFromErrorToInitialStep()
  | TransitionFromErrorToDoneStep()
  | TransitionFromInitialToDoneStep()

predicate NextStep(v:Variables, v':Variables, step:Step)
  requires Valid(v)
{
  match step
	  case TransitionFromInitialToErrorStep() => TransitionFromInitialToError(v, v')
	  case TransitionFromErrorToErrorStep() => TransitionFromErrorToError(v, v')
	  case TransitionFromErrorToInitialStep() => TransitionFromErrorToInitial(v, v')
	  case TransitionFromErrorToDoneStep() => TransitionFromErrorToDone(v, v')
	  case TransitionFromInitialToDoneStep() => TransitionFromInitialToDone(v, v')
}

predicate Next(v:Variables, v':Variables)
  requires Valid(v)
{
  exists step :: NextStep(v, v', step)
}

predicate Valid(v:Variables)
{
    && (v.state == Initial || v.state == Error ==> v.success == 0)
    && (v.state == Done ==> v.success == 1)
    && v.write >= 0
    && v.read >= 0
    && (v.write > v.read ==> v.write - v.read <= 2)
}

predicate ValidTransition(v:Variables, v':Variables)
{
    && v.read - v'.read <= 1
    && v.write - v'.write <= 1
    && v'.success - v.success <= 1
    && v.read + v.write > v'.read + v'.write
}

lemma SafetyProof()
ensures forall v | Init(v) :: Valid(v)
ensures forall v, v' | Valid(v) && Next(v, v') && ValidTransition(v,v') :: Valid(v')
{
}

type Trace = nat -> Variables

ghost predicate IsTrace(trace: Trace)
{
    Init(trace(0)) &&
    forall i: nat :: Valid(trace(i)) && Next(trace(i), trace(i+1)) && ValidTransition(trace(i), trace(i+1)) ==> Valid(trace(i+1))
}

lemma SafetyProofTrace(trace: Trace)
    requires Init(trace(0))
{
    // Base case:
    assert Init(trace(0));
    assert Valid(trace(0));

    assert Valid(trace(0)) && Next(trace(0), trace(1)) ==> Valid(trace(1)) && ValidTransition(trace(0), trace(1));
    assert Valid(trace(1)) && Next(trace(1), trace(2)) ==> Valid(trace(2)) && ValidTransition(trace(1), trace(2));

    // Inductive step:
    forall i | i >= 0
        ensures Valid(trace(i)) && Next(trace(i), trace(i+1)) && ValidTransition(trace(i), trace(i+1)) ==> Valid(trace(i+1)) 
    {
        if Valid(trace(i)) && Next(trace(i), trace(i+1)){
            assert trace(i).success <= 1;
            if trace(i+1).state == Done {
                assert trace(i+1).success == 1;
            }
        }
        assert Valid(trace(i)) && Next(trace(i), trace(i+1)) && ValidTransition(trace(i), trace(i+1)) ==> Valid(trace(i+1));
        if Valid(trace(i)) && Next(trace(i), trace(i+1)) && Valid(trace(i+1)) && ValidTransition(trace(i), trace(i+1)) {
            assert trace(i).read + trace(i).write > trace(i+1).read + trace(i+1).write; 
            assert trace(i+1).success <= 1;
        }
    }
}

// Assume that the network errors will eventually correct
ghost predicate FairNetwork(trace: Trace) 
{
    IsTrace(trace) &&
    forall n: nat :: HasDone(n, trace)
}

ghost predicate HasDone(n: nat, trace: Trace)
{
    exists n' :: n <= n' && trace(n').state == Done && trace(n').success == 1
}

lemma LivenessProof(trace: Trace, n: nat)
        returns (n': nat)
    requires IsTrace(trace) && FairNetwork(trace)
    requires Init(trace(n))
    requires forall i: nat :: i >= n ==> (Valid(trace(i)) && Next(trace(i), trace(i+1)))
    ensures n <= n' && trace(n').state == Done && trace(n').success == 1
{
    n' := n;
    while true
        invariant n <= n'
        invariant (Valid(trace(n)) && Next(trace(n), trace(n+1)))
        invariant Valid(trace(n')) && Next(trace(n'), trace(n'+1)) && ValidTransition(trace(n'), trace(n'+1)) && Valid(trace(n'+1))
        decreases if Valid(trace(n')) && Next(trace(n'), trace(n'+1)) && Valid(trace(n'+1)) && ValidTransition(trace(n'), trace(n'+1)) then trace(n').read + trace(n').write else 0
    {
        SafetyProofTrace(trace);
        var prev := trace(n').read + trace(n').write;
        var prev_n := n';

        n' := n' + 1;

        assert (trace(n').read + trace(n').write) < prev;

        if trace(n').state == Done {
            assert trace(n').success == 1;
            break;
        }
    }
    assert trace(n').state == Done;
    assert trace(n').success == 1;
}

