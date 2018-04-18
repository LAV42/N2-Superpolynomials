`type/pN2spart` := proc(spart)
    return isSpartValid(spart);
end proc:

`type/a_indet` := proc(a) local bool;
	if convert(a,string)[1] = "a" and type(a,indexed) then bool:=true; else bool:=false; end if;
	return bool; 
end proc:

`type/b_indet` := proc(a) local bool;
	if convert(a,string)[1] = "b" and type(a,indexed) then bool:=true; else bool:=false; end if;
	return bool; 
end proc:
`type/z_var` := proc(expr) local bool;
	bool:=false;
	if convert(expr, string)[1]= "z" and type(expr, commutative) and nops(indets(expr)) <2 and degree(expr)=1 then bool:=true; end if; 
	return bool;
end proc:

`type/AC_phi` := proc(expr) local bool;
	bool:=false; 
	if convert(expr, string)[1..3] = "phi" and type(expr, anticommutative) and nops(indets(expr)) <2 then bool:= true; end if;
	return bool;
end proc:

`type/AC_theta` := proc(expr) local bool;
	bool:=false; 
	if convert(expr, string)[1..3] = "the" and type(expr, anticommutative) and nops(indets(expr)) <2 then bool:= true; end if;
	return bool;
end proc:

`type/powersum_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..2] = "p[" and type(expr,indexed) then bool := true; else bool:= false; end if;
    return bool;
end proc:

`type/monomial_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..2] = "m[" and type(expr, indexed) then bool := true; else bool := false; end if;
    return bool;
end proc:

`type/homogeneous_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..2] = "h[" and type(expr, indexed) then bool := true; else bool := false; end if;
    return bool;
end proc:

`type/elementary_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..2] = "e[" and type(expr, indexed) then bool := true; else bool := false; end if;
    return bool;
end proc:
`type/g_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..2] = "g[" and type(expr, indexed) then bool := true; else bool := false; end if;
    return bool;
end proc:

`type/schur_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..2] = "s[" and convert(expr,string)[2] <> "b" and type(expr, indexed) then bool := true; else bool := false; end if;
    return bool;
end proc:

`type/schurEtoile_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..4] = "sEt[" and type(expr, indexed) then bool := true; else bool := false; end if;
    return bool;
end proc:

`type/schurbar_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..5] = "sbar[" and type(expr, indexed) then bool := true; else bool := false; end if;
    return bool;
end proc:
`type/schurbarEtoile_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..7] = "sbarEt[" and type(expr, indexed) then bool := true; else bool := false; end if;
    return bool;
end proc:

`type/ep_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..3] = "ep[" and type(expr, indexed) then bool := true; else bool := false; end if;
    return bool;
end proc:

`type/ph_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..3] = "ph[" and type(expr, indexed) then bool := true; else bool := false; end if;
    return bool;
end proc:

`type/jack_symbolic` := proc(expr) local bool;
	if convert(expr,string)[1..2] = "P[" and type(expr, indexed) then bool := true; else bool := false; end if;
end proc:

`type/superbase` := proc(expr) local bool;
	bool:= type(expr, monomial_symbolic) or type(expr, powersum_symbolic) or type(expr, elementary_symbolic) or type(expr, homogeneous_symbolic) or type(expr, g_symbolic) or type(expr, schur_symbolic) or type(expr, schurEtoile_symbolic) or type(expr, schurbar_symbolic) or type(expr, schurbarEtoile_symbolic) or type(expr, ep_symbolic) or type(expr, ph_symbolic) or type(expr, jack_symbolic);
	return bool; 
end proc:

`type/superindexed`:= proc(expr) local bool;
	bool:= type(expr, indexed) and type([op(expr)], pN2spart);
	return bool;
end proc:


super_whattype:= proc(expr)
	local element_of_basis, sample, types, which_one, the_one;
	element_of_basis:= indets(expr, superbase);
	if nops(element_of_basis) = 0 then return other; end if;
	sample:= element_of_basis[1];
	types:= [
				powersum_symbolic, 
				monomial_symbolic, 
				homogeneous_symbolic, 
				elementary_symbolic, 
				g_symbolic, 
				schur_symbolic, 
				schurEtoile_symbolic, 
				schurbar_symbolic, 
				schurbarEtoile_symbolic, 
				ep_symbolic,
				ph_symbolic,
				jack_symbolic
			];
	which_one:= map(x-> type(sample, x), types);
	the_one:= ListTools:-Search(true, which_one);
	return types[the_one]; 
end proc:
