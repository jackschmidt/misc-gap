##############################################################################
##
##  MinimalSubsetSatisfyingSupersetClosedPredicate( set, predicate )
##
##  Return a list of all subsets of set satisfying the predicate
##  but which have no proper subset satisfying the predicate, assuming
##  that every super-set of a subset also satisfies the predicate.
##
##  For example, finding minimal generating sets could be done using
##  the predicate "Does this subset generate?"
##
##  Algorithm: not particularly optimized. Builds up from nothing,
##  finding all prefix minimal sequences, and then filters out to
##  find minimal subsets.
##
MinimalSubsetSatisfyingSupersetClosedPredicate := function( set, pred )
  local recurse, prefix_minimal;

  recurse := function( sub, ind )
    local ret, i, newsub;
    if pred(sub) then return [ sub ]; fi;
    ret := [];
    for i in [ind..Length(set)] do
      newsub := Concatenation(sub, set{[i]});
      Append( ret, recurse( newsub, i+1 ) );
    od;
    return ret;
  end;

  prefix_minimal := recurse( [], 1 );
  return Filtered( prefix_minimal, x -> ForAll( prefix_minimal, y ->
    Size(x) <= Size(y) or not IsSubset(x,y) ) );
end;

##############################################################################
##
##  MinimalFaithfulLinearCharacterUsingChars( chars )
##
##  Given a list of (usually irreducible) characters, find a character that
##  (1) is a sum of those characters
##  (2) is faithful
##  (3) has minimal degree amongst all solutions to (1) and (2)
##
##  Typically, you would call this as:
##
##  chi := MinimalFaithfulLinearCharacterUsingChars( Irr( grp ) );
##
##  If you wanted to use other fields, you could adjust chars here
##  using Galois sums. If you only wanted to allow certain characters,
##  possibly reducible, that is also allowed (they should be characters
##  though, not just class functions).
##
##  Algorithm: Since the kernel of a character is determined only
##  by its constituents, and is independent of their (non-zero)
##  multiplicities, all solutions to (1) and (2) of minimal degree
##  are multiplicity-free: they are just a sum of distinct given characters.
##
##  Hence we find all minimal subsets of the given characters whose
##  sum is faithful, check their degrees, and take one of minimal
##  degree.
##
MinimalFaithfulLinearCharacterUsingChars := function( chars )
  local minker, mindeg, chi;
  minker := MinimalSubsetSatisfyingSupersetClosedPredicate( chars,
    subset -> Size(subset) > 0 and Size(ClassPositionsOfKernel(Sum(subset))) = 1 );
  mindeg := Minimum( List( minker, subset -> Degree(Sum(subset)) ) );
  chi := Sum( First( minker, subset -> Degree(Sum(subset)) = mindeg ) );
  return chi;
end;

##############################################################################
##
##  MinimalFaithfulLinearDegree( grp )
##
##  Returns the minimum number n such that grp has a faithful linear
##  representation over the complex numbers of degree (dimension) n.
##
MinimalFaithfulLinearDegree := function( grp )
  return Degree( MinimalFaithfulLinearCharacterUsingChars( Irr( grp ) ) );
end;

##############################################################################
##
##  LinearRepresentationFromCharacter( chi )
##
##  Apply the Dixon algorithm to convert the irreducible constituents of chi
##  into representations (group homomorphisms) and then sums them up using
##  block matrices.
##
LinearRepresentationFromCharacter := function( chi )
  local grp, irrs, mults, reps, gens, imgs, i, mul, phi, j, img, k;
  irrs := ConstituentsOfCharacter(chi);
  mults := MatScalarProducts( irrs, [chi] )[1];
  grp := UnderlyingGroup(chi);
  reps := IrreducibleRepresentationsDixon(grp, irrs);
  gens := GeneratorsOfGroup( grp );
  imgs := List( gens, x -> fail );
  for i in [1..Size(mults)] do
    mul := mults[i];
    phi := Irr(grp)[i];
    for j in [1..Size(gens)] do
      img := Image(reps[i], gens[j]);
      for k in [1..mul] do
        if imgs[j] = fail
        then imgs[j] := img;
        else imgs[j] := DirectSumMat( imgs[j], img );
        fi;
      od;
    od;
  od;
  return GroupHomomorphismByImages( grp, gens, imgs );
end;
