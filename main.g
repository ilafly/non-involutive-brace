LoadPackage("YangBaxter");

distribute_right:= function(br, a)
  local b,c,x;
  for b in AsList(br) do
    for c in List(SkewbraceAList(br), x -> SkewbraceElmConstructor(br, x)) do
      if (b+c)*a <> b*a - a + c*a then
        return false;
      fi;
    od;
  od;
  return true;
end;

are_the_same:= function(br,w,z)
  local a;
  for a in List(SkewbraceAList(br), x -> SkewbraceElmConstructor(br, x)) do
    if a*w - a*z <> w-z then
      return false;
    fi;
  od;
  return true;
end;


sigma:=function(br,x,y,z)
      return x*y-x*z+z;
end;

Skewbrace2newYB:=function(obj, z)
  local a, b, x, y, u, v, add, set, tmp_r, tmp_l, lperms, rperms, yb;

  add := AsList(obj);
  set := [1..Size(obj)];

  lperms := [];
  rperms := [];

  for a in AsList(obj) do

    tmp_l := [];
    tmp_r := [];

    for b in AsList(obj) do
      Add(tmp_l, Position(AsList(obj), sigma(obj,a,b,z)));
      Add(tmp_r, Position(AsList(obj), sigma(obj,a,b,z)^(-1)*a*b));
    od;
    Add(lperms, tmp_l);
    Add(rperms, tmp_r);
  od;

  lperms := List(lperms, PermList);
  rperms := List(TransposedMat(rperms), PermList);

  yb := Permutations2YB(lperms, rperms);
  SetLabels(yb, AsList(obj));

  return yb;
end;

is_homomorphism := function(f, x, y)
  local i, j;
  for i in [1..Size(x[1])] do
    for j in [1..Size(x[1])] do
      if f[x[1][i][j]] <> y[1][f[i]][f[j]] then
        return false;
      fi;
       if f[x[2][i][j]] <> y[2][f[i]][f[j]] then
        return false;
      fi;
    od;
  od;
  return true;
end;

are_isomorphic := function(x, y)
  local n,p,f;
  if Size(x[1]) <> Size(y[1]) then
    return false;
  else
    n := Size(x[1]);
    for p in SymmetricGroup(n) do
      if p = [] then
        f := [1..n];
      else
        f := ListPerm(p,n);
      fi;
      if is_homomorphism(f, x, y) then
        return true;
      fi;
    od;
  fi;
  return false;
end;

is_new := function(list, x)
  local y;
  for y in list do
    if are_isomorphic(x, y) then
      return false;
    fi;
  od;
  return true;
end;

clean := function(list)
  local x, new;
  new := [];
  for x in list do
    if is_new(new, x) then
      Add(new, x);
    fi;
  od;
  return new;
end;

allsolutions:=function(n)
  local a, br, sol, sols;
  sols:=[];
  for br in AllSmallSkewbraces(n) do
    sol := Skewbrace2YB(br);
    Add(sols, [LMatrix(sol), RMatrix(sol)]);
    for a in AsList(br) do
      if a in Socle(br) then
      else
        if IsTwoSided(br) then
          sol := Skewbrace2newYB(br,a);
          Add(sols, [LMatrix(sol), RMatrix(sol)]);
        elif distribute_right(br,a) then
          sol := Skewbrace2newYB(br,a);
          Add(sols, [LMatrix(sol), RMatrix(sol)]);
        fi;
      fi;
    od;
  od;
  return clean(sols);
end;

allclassicalsolutions:=function(n)
  local br, sol, sols;
  sols:=[];
  for br in AllSmallSkewbraces(n) do
    sol := Skewbrace2YB(br);
    Add(sols, [LMatrix(sol), RMatrix(sol)]);
  od;
  return clean(sols);
end;


test:=function(br)
  local a, sol, list;
  for a in AsList(br) do
    sol:=Skewbrace2newYB(br,a);
    Print(LMatrix(sol), "\n");
  od;
end;

#Some code for finding the right distributing elements (Far from perfect)

Sbe:= function(br, a)
  local b,c,x;
  for b in AsList(br) do
    for c in List(SkewbraceAList(br), x -> SkewbraceElmConstructor(br, x)) do
      if (b+c)*a<>b*a-a+c*a then
        return false; 
      fi;
    od;
  od;
  return true;
end;

ParTest:=function(a)
	local b, br;
	for br in AllSmallSkewbraces(a) do IsTwoSided(br); IsTrivialSkewbrace(br); Print("\nNew brace:","\nIs two sided? ", IsTwoSided(br)," Is trivial? ", IsTrivialSkewbrace(br), "\nElements: ");
		for b in br do Sbe(br,b); Print(Sbe(br,b)," "); 
		od; 
	od; 
end;

ParTest2:=function(a)
	local b, br;
	for br in AllSmallSkewbraces(a) do IsTwoSided(br); IsTrivialSkewbrace(br); IsClassical(br); Print("\nNew brace:","\nIs two sided? ", IsTwoSided(br)," Is trivial? ", IsTrivialSkewbrace(br), " Is abelian? ", IsClassical(br), "\nElements: ");
		if IsTwoSided(br)<>true then
			for b in br do Sbe(br,b); Print(Sbe(br,b)," "); 
			od;
		else 
			Print("TWO-SIDED"); 
		fi; 
	od; 
end;



# IsTwoSided
# IsClassical
# IsTrivialSkewbrace
