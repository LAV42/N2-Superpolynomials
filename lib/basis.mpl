###########################
# Fonctions on polynomials#
###########################






######################################################
## Definition of basis on directly on the coordinates#
######################################################
m_in_z:= proc(spart::pN2spart,forceVars:=`MORE`)
	local sector,part_phi, part_phitheta, part_theta, part_zed, monome_length, nbVars, perm_indices, supermonome, lem, lemprime, ledegree, part_pt, mbarbar; remember;
	# This procedure produces the monomial in terms of the variables
	# This requires the procedure partial_monomial
	with(Physics);
	part_pt:= spart[1];
	part_phi:=spart[2];
	part_theta:=spart[3];
	part_zed:=spart[4];
	monome_length:=nops(Flatten(spart));
	if forceVars= `MORE` then 
		sector:= giveSpartSector(spart);
        	ledegree:= sector[1];
		lem:= sector[2];
		lemprime:= sector[3];
		mbarbar:= sector[4];
        	nbVars:= max(map(x-> nops(Flatten(x)), genN2spart(ledegree, lem, lemprime, mbarbar)));
	else
		if forceVars=`MIN` then 
	    		nbVars:= monome_length; 
           		if nbVars=1 then nbVars:= nbVars+1; end if;
	    	else
	    		if forceVars<monome_length then
				print("Error[1]: Forced number of variable invalid");
				print(" minimal number of variables set instead"); 
				nbVars:=monome_length;
			else
				nbVars:=forceVars;
			end if;
		end if;
	end if;
	supermonome:= partial_monomial(switch_notation(spart,a));
	supermonome:= Kw(supermonome, nbVars);
	return supermonome;
end proc:
partial_monomial:= proc(spart)
	local the_indices, a_monomial,k, part_mono;
	#Creates the first monomial to be symmetrized, the spart going in the argument must be written in terms of the TC spart notation
	the_indices:= [seq(k, k=1..nops(spart))];
	a_monomial := map(x-> 
		if 	spart[x][2] = "T" 	then (phi||x)*(z||(x))^(spart[x][1]);
		elif 	spart[x][2] = "C" 	then (theta||x)*(z||(x))^(spart[x][1]);
		elif 	spart[x][2] = "TC" 	then (phi||x)*(theta||x)*(z||x)^(spart[x][1]);
		elif 	spart[x][2] = "" 	then (z||x)^(spart[x][1]);
		end if, the_indices);
	part_mono:=1; for k in a_monomial do part_mono:= part_mono*k; end do;
	return sort(part_mono); 
end proc: 

p_in_z:= proc(spart,forceVars:=0,factoring:=0,help:=0) 
	#Produces the powersums in terms of the variables
	local sector,phipart,phithetapart,thetapart,zedpart,nbVar,prod,phis,thetas, phithetas,zed,part,Vars, Lambda, powersums, powersum, k; option remember;
	if help <> 0 then
		p2nHelp();
		return NULL;
	end if;
	if spart = [[],[],[],[0]] then return 0; end if;
	sector:= giveSpartSector(spart);
	nbVar:= max(map(x-> nops(Flatten(x)), genN2spart(op(sector)))); 
	if forceVars>nbVar then nbVar:=forceVars; end if;
	if forceVars<>0 then nbVar:=forceVars; end if;
	Lambda:= switch_notation(spart,a);
	powersums:= map(x-> nth_powersum(x, nbVar), Lambda);

	#specific to our symmetry
	#subzero:= {seq(phi||k*theta||k = 0, k=1..nbVar)};
	if factoring <> 0 then 
		powersum:= mul(k, k in powersums);
		#powersum:= PerformOnAnticommutativeSystem(mul,[k, k in powersums]);
	else
		powersum:=1;
		for k in powersums do
			powersum:= sort(expand(powersum*k));
			powersum:= powersum - add(phi||k*theta||k*diff(diff(powersum,phi||k),theta||k),k=1..nbVar);
		end do:
	end if;
	return sort(expand(powersum));
end proc:
nth_powersum:= proc(a_part, nbvar); 
	#Gives the n_th powersums ex: \bar{p}_3 = (phi_1z_1^3 + ...)
	if a_part[2] = "" then 
		#return add( (z||k)^a_part[1], k=1..nbvar);
		return m_in_z([[],[],[a_part[1]]],nbvar);
	elif a_part[2] = "T" then
		#return add( phi||k*(z||k)^a_part[1], k=1..nbvar);
		return m_in_z([[a_part[1]],[],[]], nbvar);
	elif a_part[2] = "C" then
		#return add( theta||k*(z||k)^a_part[1], k=1..nbvar);
		return m_in_z([[],[a_part[1]],[]], nbvar);
	elif a_part[2] = "TC" then
		return add( tau||k*psi||k*x^(a_part[1]), k=1..nbvar); 
	end if;
end proc:

z_to_p:= proc(inpoly)
	local powersums, pre_soln, pre_solnzed, polyinp,a, k, laspart,Vars, nbvars, poly, phis, thetas, zeds, lem, mprime, degreeSym, degreeFerm, sparts, monomials, syseq, soln, polyinm;
	option remember;
	# Takes a polynomial in the variables in solve it in terms of powersums 
	poly:= inpoly;
	Vars:= giveVars(poly);
	if inpoly=0 then return 0; end if;
	nbvars:= max(nops(Vars[1]), nops(Vars[2]), nops(Vars[3]));
	phis:=Vars[1];
	thetas:=Vars[2];
	zeds:=Vars[3];
	if nbvars = 0 then return 1; end if; 
    	lem:=         nops(giveVars(op(1,sort(expand(poly))))[1]); 
    	mprime :=   nops(giveVars(op(1,sort(expand(poly))))[2]);
	degreeFerm:= lem+mprime;
    	degreeSym:= degree(poly, zeds);
    	sparts:= genN2spart(degreeSym, lem, mprime, mbarbar);

    	sparts:= map(x-> if nops(Flatten(x)) > nbvars then NULL; else x; end if, sparts);
    	powersums:= map(x-> p[op(x)] = p_in_z(x, nbvars), sparts);
	pre_soln:=add(a[k]*p[op(sparts[k])], k=1..nops(sparts)) ;
	pre_solnzed:= subs(powersums, pre_soln);
    	syseq:= pre_solnzed - poly;
    	syseq:= sort(expand(syseq));
   	soln:= superSolve(syseq);
	polyinp:= subs(soln, pre_soln); 
	return polyinp;
end proc:

old_z_to_m:= proc(inpoly, mixed:=0)
	local pre_soln, pre_solnzed,a, k, laspart,Vars, nbvars, poly, phis, thetas, zeds, lem, mprime, degreeSym, degreeFerm, sparts, monomials, syseq, soln, polyinm;
	option remember;
	#Converts a polynomial in the variables in terms of monomial symetric functions
	#Old procedure, the new one is better, kept to make sure the new one works well. 
	poly:= inpoly;
	Vars:= giveVars(poly);
	if inpoly=0 then return 0; end if;
	nbvars:= max(nops(Vars[1]), nops(Vars[2]), nops(Vars[3]));
	phis:=Vars[1];
	thetas:=Vars[2];
	zeds:=Vars[3];
	if nbvars = 0 then return 1; end if; 
    	lem:=         nops(giveVars(op(1,expand(poly)))[1]); 
    	mprime :=   nops(giveVars(op(1,expand(poly)))[2]);
	degreeFerm:= lem+mprime;
    	degreeSym:= degree(poly, zeds);
    	sparts:= genN2spart(degreeSym, lem, mprime);

    	sparts:= map(x-> if nops(Flatten(x)) > nbvars then NULL; else x; end if, sparts);
    	monomials:= map(x-> m[op(x)] = m_in_z(x, nbvars), sparts);
	pre_soln:=add(a[k]*m[op(sparts[k])], k=1..nops(sparts)) ;
	pre_solnzed:= subs(monomials, pre_soln);
    	syseq:= pre_solnzed - poly;
    	syseq:= sort(expand(syseq));
   	soln:= superSolve(syseq);
	polyinm:= subs(soln, pre_soln); 
	return polyinm;
end proc:

one_e2m:= proc(spart)
	option remember;
	local thetas, zeds, fermion_sparts, boson_sparts, mul_chain, resulting_monos, k, pts, phis, sparts;
	#Works only for N=1
	pts:= spart[1];
	phis:= spart[2];
	if pts <> [] or phis <> [] then return "ERROR: e2m not implemented for N=2"; end if; 
	thetas:= spart[3];
	zeds:= spart[4];
	fermion_sparts:=	map(x-> m[[],[],[0],[seq(1, i=1..x)]], thetas);
	boson_sparts:=		map(x-> m[[],[],[],[seq(1, i=1..x)]], zeds);
	mul_chain := [op(fermion_sparts), op(boson_sparts)];
	mul_chain:= Reverse(mul_chain);
	resulting_monos:= mul_chain[1];
	for k from 2 to nops(mul_chain) do 
		resulting_monos:= one_mono_on_expr_prod(mul_chain[k], resulting_monos);
	end do:
	return resulting_monos;
end proc:
e_en_m:= proc(spart)
	option remember;
	return one_e2m(spart); 
end proc:

e2m:= proc(expr)
	local elementaries, sparts, convertin, sublist, expr_out;
	elementaries:= [op(indets(expr, elementary_symbolic))]; 
	sparts:= map(x-> [op(x)], elementaries); 
	convertin:= map(x-> one_e2m(x), sparts); 
	sublist:= map(x-> elementaries[x] = convertin[x], [seq(k, k=1..nops(elementaries))]);
	expr_out:= subs( { op(sublist) }, expr);
	expr_out:= collect_monomials(expr_out);
	return expr_out;
end proc:

m_en_e:= proc(spart)
	local all_sparts, ep_m, ep_ep, preAns, systeq, allindets; 
	option remember;
	all_sparts:= genN2spart(op(giveSpartSector(spart)));
	ep_m:= map(x-> a[x]*e_en_m(all_sparts[x]), [seq(i, i=1..nops(all_sparts))]);
	ep_ep:= map(x-> e[op(x)], all_sparts);
	preAns:= add(a[k]*ep_ep[k], k=1..nops(all_sparts));
	systeq:= collect_monomials(m[op(spart)]- add(k, k in ep_m)); 
	allindets:= solve_monomialeq(systeq);
	return subs(allindets, preAns); 
end proc:
m_en_h:= proc(spart)
	local all_sparts, ep_m, ep_ep, preAns, systeq, allindets; 
	option remember;
	all_sparts:= genN2spart(op(giveSpartSector(spart)));
	ep_m:= map(x-> a[x]*h_en_m(all_sparts[x]), [seq(i, i=1..nops(all_sparts))]);
	ep_ep:= map(x-> h[op(x)], all_sparts);
	preAns:= add(a[k]*ep_ep[k], k=1..nops(all_sparts));
	systeq:= collect_monomials(m[op(spart)]- add(k, k in ep_m)); 
	allindets:= solve_monomialeq(systeq);
	return subs(allindets, preAns); 
end proc:

#Faire m2e 
e2p:= proc(expr)
	return collect_powersums(m_to_p(e2m(expr))); 
end proc:


one_p2m:= proc(spart)
	option remember;
	local nota_spart, chain_sparts, chain_spartR, the_chain, resulting_monos, k;
	if spart = [[],[],[],[]] then return 1; end if;
	#Take a superpartition in and expresse the powersum represented by it in terms of monomial symetric functions
	#The basis transformation is obtained with the rules for the product of two monomials. Theses rules are stated in https://arxiv.org/abs/1511.05002
	nota_spart:= switch_notation(spart);
	chain_sparts:= map(x-> [x], nota_spart);
	chain_spartR:= map(x-> reverse_notation(x), chain_sparts);
	the_chain:= Reverse(chain_spartR);
	the_chain:= map(x-> m[op(x)], the_chain);
	resulting_monos:= the_chain[1];
	for k from 2 to nops(the_chain) do
		resulting_monos:= one_mono_on_expr_prod(the_chain[k], resulting_monos);
	end do:
	return resulting_monos;
end proc:

row_p2m:= proc(expr_monomial, sparts)
	#Produces a row of the transition matrix
	return map(x-> coeff(expr_monomial, m[op(x)]), sparts);
end proc:

transition_matrix_p2m:= proc(n, mbar, mubar, mbarbar)
	option remember;
	local sparts, the_matrix;
	#Generate the transition matrix of powersums to monomials
	sparts:=genN2spart(n,mbar, mubar, mbarbar);
	the_matrix:= map(x->row_p2m(one_p2m(x), sparts), sparts);
	the_matrix:= Matrix(the_matrix);
	return the_matrix;
end proc:

transition_matrix_m2p:= proc(n, mbar, mubar, mbarbar)
	option remember;
	local the_matrix_inv, the_matrix;
	#Obtain the transition matrix of monomials to powersums
	#It is obtained by inversion of the p to m matrix
	the_matrix_inv:= transition_matrix_p2m(n, mbar, mubar, mbarbar);
	the_matrix:= LinearAlgebra[MatrixInverse](the_matrix_inv);
	return the_matrix;
end proc:

p_to_m:= proc(expr)
	local powersums, sector, sparts, monomials, transition_matrix, mono_expansion, sublist, out;
	#Takes a linear expression of powersums and converts it in terms of monomial using the transition matrix 
	powersums:= indets(expr, powersum_symbolic);
	sector:= giveSpartSector([op(powersums[1])]); 
	sparts:= genN2spart(op(sector));
	powersums:= Vector(map(x-> p[op(x)], sparts));
	monomials:= Vector(map(x-> m[op(x)], sparts));
	transition_matrix:= transition_matrix_p2m(op(sector));
	mono_expansion:= transition_matrix.monomials;
	mono_expansion:=convert(mono_expansion, list);
	powersums:= convert(powersums,list);
	sublist:= map(x-> powersums[x] = mono_expansion[x], [seq(k,k=1..nops(sparts))]); 
	out:= collect_monomials( subs(sublist, expr)); 
	return out;
end proc:

m_to_p:= proc(expr)
	local power_expansion,powersums, sector, sparts, monomials, transition_matrix, mono_expansion, sublist, out;
	#Takes a linear superposition of monomials and converts it to powersums. Uses the the transition matrix
	monomials:= indets(expr, monomial_symbolic);
	sector:= giveSpartSector([op(monomials[1])]); 
	sparts:= genN2spart(op(sector));
	powersums:= Vector(map(x-> p[op(x)], sparts));
	monomials:= Vector(map(x-> m[op(x)], sparts));
	transition_matrix:= transition_matrix_m2p(op(sector));
	power_expansion:= transition_matrix.powersums;
	power_expansion:=convert(power_expansion, list);
	monomials:= convert(monomials,list);
	sublist:= map(x-> monomials[x] = power_expansion[x], [seq(k,k=1..nops(sparts))]); 
	out:= collect_powersums( subs(sublist, expr)); 
	return out;
end proc:
m_systeq:= proc(the_equation)
	local systeq;
	systeq:=map(x-> coeff(the_equation, x), indets(the_equation, monomial_symbolic)); 
	return systeq;
	#return solve(systeq, indets(the_equation, a_indet)); 
end proc:
superSolve:= proc(the_equation, inconnu:=a)
	local vartosolve, systEq;
	#Takes an equation the_equation = 0 = a[1]*poly(z,phi,theta) + a[2]*poly(z,phi_theta) + ... and returns the solution. The point of this is that it works with AC_Vars and doesn't require that you specify the variables to solve for. 
	systEq:={Coefficients(simplify(sort(expand(the_equation))), giveVars(the_equation,1), 'onlynonzero')};
	vartosolve:= indets(the_equation, a_indet);
	return solve(systEq, vartosolve); 
	#return 1;
end proc:

giveVars:= proc(poly, flat:=0) local zeds, phis, thetas;
	#Takes a polynomial in the variables and returns all the variables found inside. It is returned as threes sets in a list: [ {phi_i}, {theta_j}, {z_k} ] 
	zeds:= indets(poly, z_var);
	phis:= indets(poly,AC_phi);
	thetas:= indets(poly, AC_theta);
	if flat<>0 then return [ op(phis), op(thetas), op(zeds) ]; end if;
	return [phis, thetas, zeds]; 
end proc:

giveNbVars:= proc(poly)
	#Returns the number of indices of a give polynomial
	return max(map(x-> nops(x),giveVars(poly))); 
end proc:

old_LinBaseConvert:= proc(exprin, totype)
	#Takes an expression expressed on the superbasis and give it back in term of another basis. It doesn't use the transition matrix method yet
#Exemple LinBaseConvert(m[[1],[],[0],[1]] + beta/(beta+1)*m[[0],[],[1],[1]], `p`); 
	local nbVars,a_numbering, thesector, sparts, z_expr, other_indets, protecting_a, expr, out;
	expr:= exprin:
	protecting_a:=indets(expr, a_indet):
	if nops(protecting_a)<>0 then 
		a_numbering:= map(x-> op(op(x)), protecting_a):
		expr:=subs(map(k->a[k] = other_indets[k], a_numbering), expr):
	end if:
	thesector:=givePolySector(expr) ; #[ mphi, mtheta, nzed, nbVars]
	sparts:= genN2spart(op(thesector)):
	nbVars:= max( map(x-> nops(Flatten(x)), sparts) );
	if 	type(op(1,indets(expr, superbase)), monomial_symbolic) then
		z_expr:= map(x-> m[op(x)] = m_in_z(x), sparts): 
	elif 	type(op(1,indets(expr, superbase)), powersum_symbolic) then
		z_expr:= map(x-> p[op(x)]= p_in_z(x), sparts): 
	elif 	type(op(1,indets(expr, superbase)), elementary_symbolic) then
		z_expr:= map(x-> e[op(x)] =e2n(x), sparts): 
	elif 	type(op(1,indets(expr, superbase)), homogeneous_symbolic) then
		z_expr:= map(x-> h[op(x)] =h2n(x), sparts): 
	elif 	type(op(1,indets(expr, superbase)), g_symbolic) then
		#z_expr:= map(x-> g[op(x)] =g2n(x, thesector[4]), sparts): 
		#z_expr:= map(x-> p[op(x)]= p2n(x, thesector[4]), sparts): 
		print("Not yet defined");
	end if;
	#z_expr:= add(k, k in Subs({op(z_expr)}, expr)):
	if totype=`z` or totype="z" then 
		z_expr:= subs(z_expr, expr);
		if nops(protecting_a)<>0 then 
			z_expr:=subs(map(k->other_indets[k] = a[k], a_numbering), z_expr):
		end if:
			return z_expr; 
	end if;
	z_expr:= sort(expand(subs(z_expr, expr)));
	if	totype= `monomial` or totype=`m` or totype="m" then out:= collect_monomials(z_to_m(z_expr)): end if:
	if	totype= `powersum` or totype=`p` or totype="p" then out:= collect_powersums(z_to_p(z_expr)): end if:
	if	totype= `homogeneous` or totype= `h` or totype="h" then out:= z_to_h(z_expr): end if:
	if	totype= `elementary` or totype=`e` or totype="e" then out:= z_to_e(z_expr): end if:
	if 	totype= `gbasis` or totype=`g` or totype="g" then out:= z_to_g(z_expr): end if; 
	
	if nops(protecting_a)<>0 then 
		out:=subs(map(k->other_indets[k] = a[k], a_numbering), out):
	end if:
	return out:
end proc:


givePolySector:= proc(poly)
	local terms, aspart;
	#Takes an expression in terms of superbasis and returns the sector in which it lives
	terms:= indets(poly,superbase);
	aspart:= [op( op(1,terms) ) ]; 
	return giveSpartSector(aspart);
end proc:

collect_by_type:= proc(thetype, expr, normalize_by:=0)
	local collected_expr; 
	#factorize the coefficients of a expression on a basis. 
	if normalize_by = 0 then
		collected_expr:= map(factor, collect(expr, indets(expr, thetype))); 
	else
		collected_expr:= map(factor, collect(expr/coeff(expr, normalize_by), indets(expr, thetype))); 
	end if:
	return collected_expr;
end proc:

collect_galpha:= proc(expr, normalize_by:=0)
	return collect_by_type(g_symbolic, expr, normalize_by);
end proc:
collect_monomials:= proc(expr, normalize_by:=0, mode:=[1,2,3])
	local normalize;
	normalize:=0;
	if normalize_by <> 0 then
		if coeff(expr, normalize_by) = 0 then
			normalize:= 0;
		else
			normalize:= normalize_by;
		end if;
	end if;
	return super_pol_sort(collect_by_type(monomial_symbolic, expr, normalize), m, givePolySector(expr), mode); 
end proc:
collect_powersums:= proc(expr, normalize_by:=0)
	return collect_by_type(powersum_symbolic, expr, normalize_by);
end proc:


#ns Basis
nsMonome:= proc(comp_in)
	local N;
	#Returns the non-symetric monomial of the composition given as an argument
	N:= nops(comp_in); 
	return mul(z||k^(comp_in[k]), k=1..N); 
end proc:

nsJack:= proc(comp_in, N:=0)
	local solns, leading_monome, complength, poids, allcomp, smallercomp, smallermonomes, prensJack, D_nsJack, lambda_nsJack, systEQ; 
	#Returns the non-symmetric jack of a composition
	poids:= add(k,k in Flatten(comp_in)); 
	allcomp:= [seq(op(composition(poids,k)),k=1..poids)]; 
	if N <> 0 then
		complength:= N; 
	else
		if poids > nops(comp_in) then complength:= poids; else complength:= nops(comp_in); end if;
	end if; 
	allcomp:= map(x-> if nops(x) < complength then [op(x),seq(0, k=1..(complength-nops(x)))]; else x; end if, allcomp); 
	allcomp:= map(x-> permute(x), allcomp); 
	allcomp:= FlattenOnce(allcomp); 
	allcomp:= MakeUnique(allcomp); 
	smallercomp:= map(x-> if compare_bruhat(comp_in, x) = `>` then x; else NULL; end if, allcomp); 
	leading_monome:= nsMonome(comp_in); 
	smallermonomes:= map(nsMonome, smallercomp); 
	prensJack:= leading_monome + add(a[k]*smallermonomes[k], k=1..nops(smallermonomes));   
	D_nsJack:= map(x-> Dunkl_i_n(x,1, prensJack, complength), [seq(k, k=1..complength)]); 
	lambda_nsJack:= map(x-> lambdabar_i(comp_in, x, complength)*prensJack, [seq(k, k=1..complength)]); 
	systEQ:= simplify(D_nsJack - lambda_nsJack); 
	systEQ:= Coefficients(systEQ, [seq(z||k, k=1..complength)], 'onlynonzero'); 
	systEQ:= MakeUnique(systEQ);
	systEQ:= {op(systEQ)}; 
	solns:= solve(systEQ, indets(systEQ,a_indet));
	#solns:= {op(Flatten(map(x-> op(superSolve(x)),systEQ)))};
	#return leading_monome+ DotProduct(solvevect,smallermonomes); 
	return subs(solns, prensJack);
end proc:

lambdabar_i:= proc(composition, i, N)
	#Returns the eigenvalue of the operator D_i (Dunkl_i_n) 
	local lalistebeta1, lalistebeta2, comparaisonbeta1, comparaisonbeta2, lalisteun, comparaisonbeta, comparaisonun, lambdai;
	lalistebeta1:= [seq(k, k=1..(i-1))]; 
	lalistebeta2:= [seq(k,k=(i+1)..N)]; 

	comparaisonbeta1:= map(k-> if composition[k] >= composition[i] then 1; else NULL; end if, lalistebeta1); 
	comparaisonbeta2:= map(k-> if composition[k] > composition[i] then 1; else NULL; end if, lalistebeta2); 
	lambdai:= composition[i] - beta*(nops(comparaisonbeta1) + nops(comparaisonbeta2)); 
return lambdai; 
end proc:


#superJacks
term_fromPart:= proc(term::list,var_index)
	local thepart, thetype;
	#Takes a part of a superpartition and returns the partial monomial associated to it
	thepart:= term[1];
	thetype:= term[2];
	if thetype = "" then 
		return (z||var_index)^thepart;
	elif thetype = "T" then
		return phi||var_index*(z||var_index)^thepart;
	elif thetype = "C" then
		return theta||var_index*(z||var_index)^thepart;
	end if;
end proc:
ns_supermonomial_sJack:= proc(spart::pN2spart, genFermProdOnly:=1)
	local Spart, themonomial, k, thetas_index, phis_index, Scomposition;
	#Returns the [phi;theta]_lambda that precedes the nsJack in the superJack definition
	Spart:= switch_notation(spart, a);
	Scomposition:= Reverse(Spart);
	themonomial:=1;
	phis_index:= [];
	thetas_index:= [];
	for k from 1 to nops(Spart) do
		themonomial:= themonomial*term_fromPart(Scomposition[k], k);
		if op(2,Scomposition[k]) = "T" then phis_index:= [ op(phis_index), k]; end if;
		if op(2,Scomposition[k]) = "C" then thetas_index:= [ op(thetas_index), k]; end if;
	end do:
	if genFermProdOnly<>0 then
		themonomial:=subs( {seq(z||k = 1, k=1..nops(Spart))}, themonomial);
	end if:
	return [themonomial, phis_index, thetas_index];
end proc:

genSuperJack:= proc(spart::pN2spart, in_alpha:=1) 
local thesector, longest_spart, phis, thetas, zeds, scomposition, thensJack, superJack, pts, mbarbar, mbar, mubar;
option remember;
	#Slow#
	#Generates the superJack N=2 using the non-symmetric Jack method (Slow)
	thesector:=giveSpartSector(spart);
	longest_spart:=max(map(x-> nops(Flatten(x)), genN2spart(op(thesector))));
	pts:= spart[1];
	phis:= spart[2];
	thetas:= spart[3];
	zeds:= spart[4]; 
	mbarbar:= nops(pts);
	mbar:= nops(phis);
	mubar:= nops(thetas);
	scomposition:= [op(Reverse(pts)),op(Reverse(phis)), op(Reverse(thetas)), op(Reverse(zeds))]; 
	#scomposition:= [op(pts),op(phis), op(thetas), op(zeds)]; 
	if longest_spart > nops(scomposition) then
		scomposition:= [op(scomposition), seq(0, k=1..(longest_spart -nops(scomposition)))];
	end if;
	#print(scomposition);
	thensJack:= nsJack(scomposition);
	thensJack:= Var_Symmetrize(thensJack, [seq(k, k=1..mbarbar)]);
	thensJack:= AntiSymetrize(thensJack, [ seq(k+mbarbar, k=1..mbar)]);
	thensJack:= AntiSymetrize(thensJack, [ seq(k+mbarbar + mbar, k=1..mubar) ]);
	thensJack:= mul(phi||k*theta||k, k=1..mbarbar)*mul(phi||(k+mbarbar), k=1..mbar)*mul(theta||(k+mbarbar+mbar), k=1..mubar)*thensJack;
	superJack:= Kw(thensJack, longest_spart); 
	if in_alpha <> 0 then superJack:= subs(beta=1/alpha, superJack); end if;
	superJack:= collect_monomials(z_to_m(superJack), m[op(spart)]); 
	return superJack; 
end proc:
gen2SuperJack:= proc(spart::pN2spart, in_alpha:=0)
	local n_spart, scomposition, numbering, the_symbols, nsmono_index, nsmono, antisym_indexphi, antisym_indextheta, thesector, longest_spart, thensJack, superJack;
	n_spart:= Reverse(switch_notation(spart));
	scomposition:= map(x-> x[1], n_spart);
	numbering:= [seq(k, k=1..nops(n_spart))];
	the_symbols:= map(x-> x[2], n_spart);
	nsmono_index:= map(x-> 
			if the_symbols[x] 	= "" then NULL; 
			elif the_symbols[x]  	= "T" then [phi||x,x,phi];
			elif the_symbols[x]	= "C" then [theta||x,x, theta];
			end if,
			numbering);
	nsmono:=mul(x[1], x in nsmono_index); 
	antisym_indexphi:=	map(x-> if x[3] = phi 	then x[2]; else NULL; end if, nsmono_index);
	antisym_indextheta:=	map(x-> if x[3] = theta then x[2]; else NULL; end if, nsmono_index);
	thesector:=giveSpartSector(spart);
	longest_spart:=max(map(x-> nops(Flatten(x)), genN2spart(thesector[1], thesector[2], thesector[3])));
	if longest_spart > nops(scomposition) then
		scomposition:= [op(scomposition), seq(0, k=1..(longest_spart -nops(scomposition)))];
	end if;
	thensJack:= nsJack(scomposition);
	thensJack:= AntiSymetrize(thensJack, antisym_indexphi);
	thensJack:= AntiSymetrize(thensJack, antisym_indextheta);
	thensJack:= nsmono*thensJack;
	superJack:= Kw(thensJack, longest_spart); 
	if in_alpha <> 0 then superJack:= subs(beta=1/alpha, superJack); end if;
	superJack:= collect_monomials(z_to_m(superJack), m[op(spart)]); 
	return superJack; 
end proc:


scalar_prod_powersum:= proc(expr_1, expr_2, param:=alpha)
	local powerSums_1, powerSums_2, non_ortho, non_ortho_spart, norms, coeff_expr1, coeff_expr2;
	#Given two expression in term of p[spart], it calculates and returns the p_alpha scalar product between the 2
	powerSums_1 := indets(expr_1, powersum_symbolic) ; 	#[ p[spart], p[spart], ... ] 
	powerSums_2 := indets(expr_2, powersum_symbolic) ;
	non_ortho := powerSums_1 intersect powerSums_2 ; 	#Sends back only spart which appears in both
	if op(non_ortho) = NULL then return 0; end if ;		#Test whether they are orthogonal
	non_ortho := [op(non_ortho)];
	#if nops(non_ortho)<2 then #Ne pas utiliser la version parrallele de map lorsqu'il n'y a qu'un element
		non_ortho_spart := map(x -> [ op(x) ], non_ortho) ;	
		norms := map(x-> norm_p(x, param), non_ortho_spart) ;	#[ norm1, norm2, norm3, ...]
		coeff_expr1 := map(x -> coeff(expr_1,x), non_ortho);  #[ coeff_of(p[spart1]), coeff_of(p[spart2]), ...]
		coeff_expr2 := map(x -> coeff(expr_2,x), non_ortho);
	#else
#		non_ortho_spart := Map(x -> [ op(x) ], non_ortho) ;	#[ [spart], [spart], ...]
#		norms := Map(x-> norm_p(x), non_ortho_spart) ;	#[ norm1, norm2, norm3, ...]
#		coeff_expr1 := Map(x -> coeff(expr_1,x), non_ortho);  #[ coeff_of(p[spart1]), coeff_of(p[spart2]), ...]
#		coeff_expr2 := Map(x -> coeff(expr_2,x), non_ortho);
#	end if;
	return add(x,x in coeff_expr1*~coeff_expr2*~norms);		# *~ is the symbol for element-wise multiplication
end proc:

norm_p:= proc(spart, parameter:=alpha)
	local p_part, pt_part, t_part, zed_part, ell_lambda, big_ell, combin, partphi, partpt, parttheta, mphi, mtheta,mpt; option remember;
	#Given a spart, returns the value of the norm of a powersum associated with this spart
	if parameter = "modeqt" then return qt_zLambda(spart); end if; 
	if parameter = "modeqt2" then return qt_zLambda2(spart); end if; 
	if parameter = "mode_inc" then return N[op(spart)]; end if; 
	partphi:= op(1,spart);
	partpt:= op(2,spart);
	parttheta:= op(3,spart);
	mphi:= nops(partphi);
	mtheta:= nops(parttheta);
	mpt:= nops(partpt); 
   	big_ell:= nops(Flatten(spart)); 
	return (parameter)^(big_ell)*zlambda(spart);
end proc:
zlambda:= proc(spart)
	option remember;
	local pt_part, zed_part, pt_distPart, zed_distPart, zlambda4, zeta1, nbZeros;
	zeta1:=1;
	zlambda4:=1:
	#Calculate the z_Lambda function 
	#p_part:=spart[1];
	pt_part:=spart[1];
	#t_part:=spart[3]
	zed_part:=spart[4];
	###
	#nbZeros:= Occurrences(0, pt_part);
	#pt_part:= eliminate_zeros(pt_part);
	###
	pt_distPart:={op(pt_part)}; 	#conserve only one occurrence of each part
	zed_distPart:={op(zed_part)};
	#Occurrences(x, L) returns the number of occurrences of x in L
	#zeta1:=		mul( factorial( Occurrences(i, pt_part)), i in pt_distPart); 
	#zeta1:= z[op(pt_part)];
	zeta1:= mul(factorial(Occurrences(i,pt_part)), i in pt_distPart);
	zlambda4:= mul(i^(Occurrences(i,zed_part))*factorial(Occurrences(i,zed_part)), i in zed_distPart);
	return zeta1*zlambda4;	
end proc:

monomial_scalar_prod:= proc(expr1, expr2,param:=alpha)
	#Give the scalar product of the expression written in terms of monomial superfunctions. It uses the fast basis transformation algorithm involving the transformation matrix. 
	return scalar_prod_powersum(m_to_p(expr1), m_to_p(expr2), param); 
end proc:

qt_monomial_scalar_prod:= proc(expr1, expr2)
	return monomial_scalar_prod(expr1, expr2, "mode_inc"); 
end proc:


#### superJacks

sJack_sector:= proc(n, mbar, mubar,mbarbar, mode:=[1,2,3], in_alpha:=1)
	#Returns all the sJacks of a sector
	#To obtain the spart to which each one is associated, use the give_greatest_monomial, it will return the m[hightspart in expression]. 
	return sJack_spart(give_greatest_spart(genN2spart(n,mbar, mubar, mbarbar, mode), mode), 1, mode, in_alpha);
end proc:

sJack_spart:= proc(spart, give_all_jacks:=0, mode:=[1,2,3], in_alpha:=1)
	local all_sparts, smaller_sparts, list_with_smaller, sjacks, sparts_in_expr, eqsyst, soln, prejack, k;
	#Returns the jack associated to a spart
	# Find every smaller sparts
	# For every smaller spart, find the set of their smaller sparts
	# Sort in terms of number of smaller sparts
	# Solve bottom to top using scalar product
	all_sparts:= genN2spart(op(giveSpartSector(spart)), mode);
	smaller_sparts:= sKeep_smaller_sparts(spart, all_sparts, mode);
	list_with_smaller:=sort(map(x-> [x,op(sKeep_smaller_sparts(x, smaller_sparts, mode))], smaller_sparts));
	list_with_smaller:=[ op(list_with_smaller), [spart, op(smaller_sparts)]]; 
	sjacks:= [m[op(op(1,list_with_smaller[1]))]];
	if nops(list_with_smaller) = 1 then 
		if give_all_jacks = 0 then return op(sjacks); end if;
		if give_all_jacks <> 0 then return sjacks; end if;
	end if;
	for k from 2 to nops(list_with_smaller) do
		sparts_in_expr:= list_with_smaller[k];
		prejack:= m[ op( sparts_in_expr[1] ) ] + add(a[k]*m[ op( sparts_in_expr[k] ) ], k=2..nops(sparts_in_expr));
		eqsyst:= map(x-> monomial_scalar_prod(prejack, x), sjacks);
		soln:= solve(eqsyst, indets(prejack, a_indet));
		prejack:= collect_monomials(subs(soln, prejack),0, mode); 
		sjacks:= [op(sjacks), prejack];
	end do;
	if in_alpha <> 1 then 
		sjacks:= map(collect_monomials,subs(alpha=1/beta, sjacks));
		end if;
	if give_all_jacks <> 0 then 
		return sjacks;
	else
		return sjacks[-1]; 
	end if;
end proc:

z_to_m:= proc(expr)
	local the_sector, sparts, sparts_notation2, part_mono, mono_coeff, out;
	the_sector:= giveZPolySector(expand(expr));	
	sparts:= genN2spart(op(the_sector)); 
	sparts_notation2:= map(x-> switch_notation(x), sparts); 
	part_mono:= map(x-> partial_monomial(x), sparts_notation2); 
	mono_coeff:= map(x-> sCoeff_nsMono(x, expr), part_mono ); 
	out:= add( factor(mono_coeff[k])*m[ op(sparts[k]) ], k=1..nops(sparts)); 
	return out;
	#partial_monomials:= map(x-> partial_monomial(x), sparts_notation2); 
end proc:

sCoeff_nsMono:= proc(expr_prod, expr)
	local sdegrees, zeds, zeds_deg, AC_terms, all_vars, in_deg, a_zero_list, in_expr, theSeq, PT_terms, x;
	#Works like coeff fonction, but instead give the coefficient of a non-symmetric monomial so for exemple : 
	# > AA:= (beta+1)phi1 theta2 theta3 z1^2z2 + ....
	# > sCoeff_nsMono( phi1theta2theta3z1^2z2, AA) = (beta+1)
	in_expr:= expr;
	sdegrees:= superDegree(expr_prod, giveNbVars(expr));
	zeds:= 		[seq(z||k, k=1..nops(sdegrees))]; 
	zeds_deg:= 	map(x-> x[1], sdegrees);
	theSeq:= 	[seq(k, k=1..nops(sdegrees))];
	AC_terms:=	map(k-> 
				if op(2, sdegrees[k]) = "C" then theta||k;
				elif op(2, sdegrees[k]) = "T" then phi||k;
				elif op(2, sdegrees[k]) = "" then NULL;
				elif op(2, sdegrees[k]) = "TC" then NULL;
				end if
				, theSeq);
	PT_terms:= map(k-> if op(2, sdegrees[k]) = "TC" then k; else NULL; end if, theSeq);
	for x in PT_terms do
		in_expr:= diff(diff(in_expr, phi||x), theta||x);
	end do;
	all_vars:= 	[op(zeds), op(AC_terms)]; 
	in_deg := 	[op(zeds_deg), seq(1, k=1..nops(AC_terms))];
	a_zero_list:= 	[seq(0, k=1..nops(all_vars))];
	return coeftayl(in_expr, all_vars = a_zero_list, in_deg);
end proc:



give_greatest_monomial:= proc(poly_in_m, mode:=[1,2,3])
	local monos, sparts, thespart;
	#Returns m[lambda], where lambda is the greatest spart in the expr. 
	monos:= [op(indets(poly_in_m, monomial_symbolic) )];
	if nops(monos) = 1 then return monos[1]; end if;
	sparts:= map(x-> [ op(x)], monos);
	thespart:= give_greatest_spart(sparts, mode);
	return m[ op(thespart) ];
end proc:

give_smallest_monomial:= proc(poly_in_m)
	local monos, sparts, thespart;
	#Returns m[lambda], where lambda is the greatest spart in the expr. 
	monos:= [op(indets(poly_in_m, monomial_symbolic) )];
	if nops(monos) = 1 then return monos[1]; end if;
	sparts:= map(x-> [ op(x)], monos);
	thespart:= give_smallest_spart(sparts);
	return m[ op(thespart) ];
end proc:


giveZPolySector:= proc(expr)
	local nbVars, a_ns_mono, thedegrees, mbar, mubar, n, mbarbar;
	#Given a polynomial in terms of the variables, returns the sector in which it lives.
	nbVars:= giveNbVars(expr);
	a_ns_mono:= op(1, expr);
	thedegrees:=superDegree(a_ns_mono, nbVars);
	mbarbar:= add(k, k in map(x-> if op(2,x) = "TC" then 1; else 0; end if, thedegrees));
	mbar:= add(k, k in map(x-> if op(2,x) = "T" then 1; else 0; end if, thedegrees));
	mubar:= add(k, k in map(x-> if op(2,x) = "C" then 1; else 0; end if, thedegrees));
	n:= add( k, k in map(x-> op(1,x), thedegrees)); 
	return [n, mbar, mubar, mbarbar]; 
end proc:

superDegree:= proc(monoterm, nbVars)
	local phis, thetas, zeds, DegPhi, DegThe, DegZed, the_degrees, k, pts, indicesVar, DegPT;
	#Returns the "superdegree" of a non-symmetric monomial
	pts:= [seq(phi||k*theta||k, k=1..nbVars)];
	phis:= [ seq(phi||k, k=1..nbVars)]; 
	indicesVar := [seq(k, k=1..nbVars)];
	thetas:= [ seq(theta||k, k=1..nbVars)]; 
	thetas:= [ seq(theta||k, k=1..nbVars)]; 
	zeds:= [ seq(z||k, k=1..nbVars)]; 
	DegPhi:= map(x-> fermionic_degree(monoterm, "phi", x), indicesVar); 
	DegThe:= map(x-> fermionic_degree(monoterm,"theta", x), indicesVar); 
	DegPT:= map(x-> fermionic_degree(monoterm,"phitheta", x), indicesVar); 
	DegZed:= map(x-> degree(monoterm, x), zeds); 
	the_degrees:= [];
	for k from 1 to nbVars do
		if DegPhi[k] = 1 then 
			the_degrees:= [op(the_degrees), [DegZed[k], "T"]];
		elif DegThe[k] = 1 then 
			the_degrees:= [op(the_degrees), [DegZed[k], "C"]];
		elif DegPT[k] = 1 then 
			the_degrees:= [op(the_degrees), [DegZed[k], "TC"]];
		else 
			the_degrees:= [op(the_degrees), [DegZed[k], ""]];
		end if;
	end do;
	return the_degrees;
end proc:

fermionic_degree:= proc(term, var, var_index)
	if var = "phitheta" then
		if diff(diff(term, phi||var_index), theta||var_index) <> 0 then 
			return 1;
		else
			return 0;
		end if;
	elif var = "phi" then
		if diff(diff(term, phi||var_index), theta||var_index) <> 0 then 
			return 0;
		else
			if diff(term, phi||var_index) <> 0 then return 1; else return 0; end if;
		end if;
	elif var = "theta" then
		if diff(diff(term, phi||var_index), theta||var_index) <> 0 then 
			return 0;
		else
			if diff(term, theta||var_index) <> 0 then return 1; else return 0; end if;
		end if;
	end if;
end proc:

spart_monomial_product:= proc(spartA, spartB)
	local ledegree, overm, underm, maxlength, ValidSparts, ellA, ellB, FspartA, FspartB, PspartB, added_sparts, coeff_sparts, final_sparts, monomial_expansion ;
	protect(a,b);
	#Generate valid sparts : right here
	#ledegree:=  add(k, k in Flatten(spartA)) + add(k, k in Flatten(spartB));
   	#overm:=         nops(spartA[1]) + nops(spartA[2]) + nops(spartB[1]) + nops(spartB[2]);
   	#underm:=        nops(spartA[2]) + nops(spartA[3]) + nops(spartB[2]) + nops(spartB[3]);
   	#maxlength:=     nops(Flatten(spartA)) + nops(Flatten(spartB)); 
    	#ValidSparts:= genN2spart(overm, underm,ledegree);
    	#ValidSparts:= map(x -> if  nops(Flatten(x)) > maxlength then NULL; else x; end if, ValidSparts);
    	#Generate fillings: sub function
    	#order to get sign: in the previous subfunction 
    	#Return the monomial superposition
    	#FspartA:= map(x-> 
	ellA:= ell(spartA);
	ellB:= ell(spartB);
	FspartA:= add_zeros_spart(spartA,ellB);
	FspartB:= add_zeros_spart(spartB,ellA);
	FspartA:= switch_notation(FspartA, a);
	FspartB:= switch_notation(FspartB, b);
	PspartB:= permute(FspartB);
	added_sparts:= MakeUnique(map(x-> add_sparts_notated(FspartA,x), PspartB)); #we keep only the distinct elements hence MakeUnique
	coeff_sparts:= map(x-> give_coeff_sparts(x), added_sparts);
	added_sparts:= map(x-> if x = [] then NULL; else x; end if, added_sparts); 
	coeff_sparts:= map(x-> give_coeff_sparts(x), added_sparts);
	final_sparts:= map(x-> reverse_notation(x), added_sparts);
	monomial_expansion:= add(k, k in map(x-> coeff_sparts[x]*m[op(final_sparts[x])],[seq(l, l=1..nops(final_sparts))])); 
	return monomial_expansion;

end proc:

add_sparts_notated:= proc(spartA,spartB)
	local added_sparts, thetypes;
	added_sparts:= map(x-> 
		if ((op(2,spartA[x]) = "T") and (op(2,spartB[x]) = "C")) or ((op(2,spartA[x]) = "C") and (op(2,spartB[x]) = "T")) then
			[0,"ZERO",0,0]; 
		else
			[ 
			op(1,spartA[x])+op(1,spartB[x]), 
			cat(op(2,spartA[x]),op(2,spartB[x])), 
			op(3,spartA[x])*op(3,spartB[x]), 
			op(4,spartA[x]), 
			op(4,spartB[x])
			];
		end if
		, 
		[seq(k, k=1..nops(spartA))]);
	thetypes:= {op(map(x-> op(2,x), added_sparts))};
	if 	"TT" in thetypes or 	
		"CC" in thetypes or 
		"TCC" in thetypes or 
		"TCT" in thetypes or 
		"TTC" in thetypes or 
		"CTC" in thetypes or 
		"TCTC" in thetypes or
		"ZERO" in thetypes
		#"TC" in thetypes or 
		#"CT" in thetypes 
		then return NULL; 
	end if;
	#added_sparts:= map(x-> if x[2] = "CT" then [x[1], "TC", x[3],x[5], x[4]]; else x; end if, added_sparts);
	added_sparts:= map(x->if x[1..2] = [0, ""] then NULL; else x; end if, added_sparts);
	added_sparts:= Reverse(sort(added_sparts));
	return added_sparts;
end proc:

give_coeff_sparts:= proc(spart)
	local skimed_spart_distparts, the_coeff, part, perm_set, fermion_permutation, Card_a, epsilon, Anti_Tensor;
	if type(reverse_notation(spart),pN2spart) <> true then return 0; end if;
	skimed_spart_distparts:= {op(map(x-> x[1..2], spart))};
	the_coeff:=1;
	for part in skimed_spart_distparts do
		perm_set:= map(x-> if part = x[1..2] then x[3]; else NULL; end if, spart);
		the_coeff:= nops({op(permute(perm_set))})*the_coeff;
	end do:
	fermion_permutation:= Flatten(map(x-> x[-2..-1], spart));
	#fermion_permutation:= Flatten(subs({a=NULL, b=NULL}, fermion_permutation)); 
	fermion_permutation:= map(x-> if type(x,a_indet) or type(x,b_indet) then x; else NULL; end if, fermion_permutation);
	Card_a:= nops(indets(fermion_permutation,a_indet));
	fermion_permutation:= map(x-> if type(x,a_indet) then op(x); else op(x)+Card_a; end if, fermion_permutation);
	epsilon:=1;
	if nops(fermion_permutation) >1 then 
		Anti_Tensor:=table('antisymmetric'):
		epsilon:= Anti_Tensor[op(fermion_permutation)];
		if epsilon =0  then 
			epsilon:=1;
		else
			epsilon:= coeff(epsilon, Anti_Tensor[op(sort(fermion_permutation))]);
		end if;
	end if:
	return epsilon*the_coeff:
end proc:

add_zeros_spart:= proc(spart, number_of_zeros)
	local padded_spart;
	padded_spart:= [spart[1], spart[2], spart[3], [op(spart[4]),seq( 0, k=1..number_of_zeros)]];
	return padded_spart;
end proc:

two_monomial_product:= proc(mono1, mono2)
	option remember;
	local monos_out;
	monos_out:=spart_monomial_product([op(mono1)], [op(mono2)]); 
	return monos_out:
end proc:

one_mono_on_expr_prod:= proc(mono, expr_monos)
	local right_prod_monos, sublist, out;
	right_prod_monos:= indets(expr_monos, monomial_symbolic);
	sublist:= map(x-> x=two_monomial_product(mono, x), right_prod_monos);
	out:= collect_monomials(subs(sublist, expr_monos)); 
	return out; 
end proc:

expr_mono_prod:= proc(expr1, expr2)
	local left_prod, sublist, out;
	if expr1 = 1 then return expr2; end if;
	if expr2 = 1 then return expr1; end if;
	left_prod:= indets(expr1, monomial_symbolic); 
	sublist:= map(x-> x=one_mono_on_expr_prod(x, expr2), left_prod); 
	out:= collect_monomials(subs(sublist, expr1)); 
	return out;
end proc:

isJackFromNS:= proc(expr_m)
	local spart, thesector, longest_spart, pts, phis, thetas, zeds, mbar, mubar, mbarbar, expr_z, dexpr, theIndex, thensJack, scomposition, k; option remember;
	spart:= [op(give_greatest_monomial(expr_m))];
	thesector:= giveSpartSector(spart);
	longest_spart:=max(map(x-> nops(Flatten(x)), genN2spart(op(thesector))));
	pts:= spart[1];
	phis:= spart[2];
	thetas:= spart[3];
	zeds:= spart[4];
	mbar:= thesector[2];
	mubar:= thesector[3];
	mbarbar:= thesector[4];
	expr_z:= LinBaseConvert(expr_m, `z`); 
	dexpr:= expr_z;
	for k from 1 to mbarbar do
		dexpr:= diff(diff(dexpr, phi||k), theta||k);
	end do;
	for k from 1 to mbar do
		theIndex:= k+mbarbar;
		dexpr:= diff(dexpr, phi||theIndex);
	end do;
	for k from 1 to mubar do
		theIndex:= k+mbarbar+mbar;
		dexpr:= diff(dexpr, theta||theIndex);
	end do;
	scomposition:= [op(Reverse(pts)),op(Reverse(phis)), op(Reverse(thetas)), op(Reverse(zeds))]; 
	if longest_spart > nops(scomposition) then
		scomposition:= [op(scomposition), seq(0, k=1..(longest_spart -nops(scomposition)))];
	end if;
	thensJack:= nsJack(scomposition);
	thensJack:= Var_Symmetrize(thensJack, [seq(k, k=1..mbarbar)]);
	thensJack:= AntiSymetrize(thensJack, [ seq(k+mbarbar, k=1..mbar)]);
	thensJack:= AntiSymetrize(thensJack, [ seq(k+mbarbar + mbar, k=1..mubar) ]);
	return [dexpr, thensJack];
end proc:

solve_monomialeq:= proc(expr)
	local monos, indets_expr, the_coeffs;
	monos:= indets(expr, monomial_symbolic);
	indets_expr:= indets(expr, a_indet); 
	the_coeffs:= map(x-> coeff(expr, x), monos);
	return solve(the_coeffs, indets_expr);
end proc:
t_poch:= proc(n)
	return mul( (1-t^k), k=1..n); 
end proc:

qt_zLambda2:= proc(spart)
	local zed_part, zlambda4, qtzlambda, zed_distPart, pt_part, pt_distPart, zeta1;
	pt_part:= spart[1];
	pt_distPart:=MakeUnique(pt_part); 	#conserve only one occurrence of each part
	#zeta1:= q^(add(k, k in pt_part))*mul(factorial(Occurrences(i,pt_part)), i in pt_distPart);
	#zeta1:= zeta1*mul(factorial(Occurrences(i,pt_part))/(t_poch(Occurrences(i, pt_part))), i in pt_distPart);
	zeta1:=1;
	zeta1:= zeta1*zeta[op(pt_part)]; 

	zed_part:= spart[4];
	zed_distPart:= MakeUnique(zed_part); 
	zlambda4:= mul(i^(Occurrences(i,zed_part))*factorial(Occurrences(i,zed_part)), i in zed_distPart);
	qtzlambda:=	#f[spart[2],spart[3]]*
				#zlambda4*q^(add(k, k in spart[3])+add(k,k in spart[2]))*c^(add(k, k in spart[2]))*d^(add(k, k in spart[3]));
				zlambda4*(q*t)^(-add(k, k in spart[3]))*q^(-add(k,k in spart[4]));
	#qtzlambda:=	zlambda4*q^(add(k, k in spart[3])+add(k,k in spart[2]));
	qtzlambda:= qtzlambda*mul((1-q^(x))/(1-t^(x)), x in spart[4]); 
	return subs(zeta[]=1,qtzlambda*zeta1);
end proc:
qt_zLambda:= proc(spart)
	local pts, phis, thetas, spart_s, mbar, mubar, stat1, spart_pts_dist, spart_s_dist, aut_lambdas, aut_pts, qtz;
	pts:= 		spart[1];
	phis:= 		spart[2]; 
	thetas:= 	spart[3]; 
	spart_s:= 	spart[4]; 
	mbar:= nops(phis);
	mubar:= nops(thetas); 

	spart_pts_dist:= MakeUnique(pts); 
	spart_s_dist:= MakeUnique(spart_s); 
	aut_lambdas:= mul(factorial(Occurrences(k, spart_s)), k in spart_s_dist); 
	aut_pts:= mul(factorial(Occurrences(k, pts)), k in spart_pts_dist); 

	qtz:=1;
	qtz:= aut_pts*aut_lambdas*mul(x, x in spart_s)*mul((1-q^(x))/(1-t^(x)), x in spart_s)*qtz;
	qtz:= (t)^(-1*add(k, k in phis))*q^(add(k, k in thetas))*qtz; 
	qtz:= mul((1-q^(x))/(1-t^(x)), x in subs(0=NULL, pts))*qtz;
	#qtz:= (q)^(add(k, k in pts))*qtz;
	#qtz:= factor(qtz); 
	return qtz; 
end proc:


sMacdo_sector:= proc(n, mbar, mubar,mbarbar, in_alpha:=1, mode:=1) option remember;
	#Returns all the sJacks of a sector
	#To obtain the spart to which each one is associated, use the give_greatest_monomial, it will return the m[hightspart in expression]. 
	return sMacdo_spart(give_greatest_spart(genN2spart(n,mbar, mubar, mbarbar)), 1);
end proc:

sMacdo_spart:= proc(spart, give_all_jacks:=0, mode:=0) option remember;
	local sMacs, preMac, all_sparts, smaller_sparts, list_with_smaller, sjacks, sparts_in_expr, eqsyst, soln, prejack, k;
	#Returns the macdo associated to a spart
	# Find every smaller sparts
	# For every smaller spart, find the set of their smaller sparts
	# Sort in terms of number of smaller sparts
	# Solve bottom to top using scalar product
	all_sparts:= genN2spart(op(giveSpartSector(spart)));
	smaller_sparts:= sKeep_smaller_sparts(spart, all_sparts);
	list_with_smaller:=sort(map(x-> [x,op(sKeep_smaller_sparts(x, smaller_sparts))], smaller_sparts));
	list_with_smaller:=[ op(list_with_smaller), [spart, op(smaller_sparts)]]; 
	sMacs:= [m[op(op(1,list_with_smaller[1]))]];
	if nops(list_with_smaller) = 1 then 
		if give_all_jacks = 0 then return op(sMacs); end if;
		if give_all_jacks <> 0 then return sMacs; end if;
	end if;
	for k from 2 to nops(list_with_smaller) do
		sparts_in_expr:= list_with_smaller[k];
		preMac:= m[ op( sparts_in_expr[1] ) ] + add(a[k]*m[ op( sparts_in_expr[k] ) ], k=2..nops(sparts_in_expr));
		if mode = 0 then eqsyst:= map(x-> monomial_scalar_prod(preMac, x, "modeqt"), sMacs); end if;
		if mode =1 then eqsyst:= map(x-> monomial_scalar_prod(preMac, x, "modeqt2"), sMacs); end if;
		soln:= solve(eqsyst, indets(preMac, a_indet));
		preMac:= collect_monomials(subs(soln, preMac)); 
		sMacs:= [op(sMacs), preMac];
	end do;
	if give_all_jacks <> 0 then 
		return sMacs;
	else
		return sMacs[-1]; 
	end if;
end proc:
N2toN1spart:= proc(spart)
	return [spart[3], spart[4]];
end proc:

N1toN2spart:= proc(spart)
	return [[],[],spart[1], spart[2]]; 
end proc:

N1convertexpr:= proc(expr)
	local base_elements, base_str, where, thebase, sublist;
	#
	base_elements:= indets(expr, superbase);
	if nops(base_elements) = 0 then return expr; end if;
	base_str:= convert(base_elements[1], string); 
	where:= StringTools:-Search("[", base_str); 
	thebase:= convert(base_str[1..where-1], symbol);
	sublist:= map(x-> x= thebase[op(N2toN1spart([op(x)]))], base_elements); 
	return subs(sublist, expr); 
end proc:
N2convertexpr:= proc(expr)
	local base_elements, base_str, where, thebase, sublist;
	base_elements:= indets(expr, superbase);
	if nops(base_elements) = 0 then return expr; end if;
	base_str:= convert(base_elements[1], string); 
	where:= StringTools:-Search("[", base_str); 
	thebase:= convert(base_str[1..where-1], symbol);
	sublist:= map(x-> x= thebase[op(N1toN2spart([op(x)]))], base_elements); 
	return subs(sublist, expr); 
end proc:

sSchur_en_m := proc(spart)
	option remember;
	local aschur;
	aschur:= sMacdo_spart(spart);
	aschur:= limit(limit(aschur, q=0), t=0);
	return aschur;
end proc:

sSchurBar_en_m := proc(spart)
	option remember;
	local aschur;
	aschur:= sMacdo_spart(spart);
	aschur:= limit(limit(aschur, q=infinity), t=infinity);
	return aschur;
end proc:

sSchurEtoile_en_m:= proc(spart)
	option remember;
	return collect_monomials((-1)^( nops(spart[3])*(nops(spart[3])-1)/2 )*monomial_omega_alpha(sSchurBar_en_m(SuperConjugate(spart)), 1)); 
end proc:

sSchurBarEtoile_en_m:= proc(spart)
	option remember;
	return collect_monomials((-1)^(nops(spart[3])*(nops(spart[3])-1)/2)*monomial_omega_alpha(sSchur_en_m(SuperConjugate(spart)), 1)); 
end proc:

sSchurJack_en_m:= proc(spart)
	option remember;
	local aschur;
	aschur:= sMacdo_spart(spart);
	aschur:= subs( q = t^alpha, aschur);
	aschur:= limit(aschur,t=1);
	aschur:= limit(aschur, alpha=1); 
	return aschur;
end proc:

ep_en_m := proc(spart)
	local thetas, zeds;
	option remember;
	thetas:=1;
	zeds:= 1;
	if spart[3] <> [] then
		thetas	:= (-1)^(add(k, k in spart[3]))*e2m(e[[],[],spart[3],[]]); 
	end if;
	if spart[4] <> [] then
		zeds	:= p_to_m(p[[],[],[],spart[4]]); 
	end if;
	if thetas =1 or zeds =1 then 
		return thetas*zeds; 
	else 
		return collect_monomials( expr_mono_prod(thetas, zeds) ); 
	end if;
end proc:

h_en_m:= proc(spart)
	option remember;
	local pts, phis, thetas, zeds, sparts_zeds, sparts_thetas, the_prod, spats, the_monos, sparts;
	pts:= spart[1];
	phis:= spart[2];
	thetas:= spart[3];
	zeds:= spart[4]; 
	if pts <> [] or phis <> [] then return "ERROR: h_en_m not yet defined for N=2"; end if; 
	sparts_zeds:= Reverse(map(x-> genN2spart(x,0,0,0),zeds)); 
	sparts_thetas:= Reverse(map(x-> genN2spart(x,0,1,0), thetas)); 
	the_prod:=1;
	for sparts in sparts_zeds do
		the_monos:= add(m[op(x)], x in sparts);
		the_prod:= expr_mono_prod(the_monos, the_prod);
	end do:
	for sparts in sparts_thetas do
		the_monos:= add((op(x[3])+1)*m[op(x)], x in sparts);
		the_prod:= expr_mono_prod(the_monos, the_prod);
	end do:
	return the_prod;
end proc:

m_en_ep:= proc(spart)
	local all_sparts, ep_m, ep_ep, preAns, systeq, allindets; 
	option remember;
	all_sparts:= genN2spart(op(giveSpartSector(spart)));
	ep_m:= map(x-> a[x]*ep_en_m(all_sparts[x]), [seq(i, i=1..nops(all_sparts))]);
	ep_ep:= map(x-> ep[op(x)], all_sparts);
	preAns:= add(a[k]*ep_ep[k], k=1..nops(all_sparts));
	systeq:= collect_monomials(m[op(spart)]- add(k, k in ep_m)); 
	allindets:= solve_monomialeq(systeq);
	return subs(allindets, preAns); 
end proc:

m_en_sSchur:= proc(spart)
	option remember;
	local smallers, all_sparts, schurs_m,schurs_s, preAns, systeq, allindets;
	smallers:= sKeep_smaller_sparts(spart, genN2spart(op(giveSpartSector(spart)))); 
	all_sparts:= [spart, op(smallers)]; 
	#schurs:= map(x-> s[op(x)], all_sparts); 
	schurs_m:= map(x->a[x]*sSchur_en_m(all_sparts[x]), [seq(i, i=1..nops(all_sparts))]); 
	schurs_s:= map(x-> s[op(x)], all_sparts); 
	preAns:= add( a[k]*schurs_s[k], k=1..nops(all_sparts)); 
	systeq := collect_monomials(m[op(spart)]-add(k, k in schurs_m)); 
	allindets:= solve_monomialeq(systeq); 
	return subs(allindets, preAns); 
end proc:

m_en_sSchurBar:= proc(spart)
	option remember;
	local smallers, all_sparts, schurs_m,schurs_s, preAns, systeq, allindets;
	smallers:= sKeep_smaller_sparts(spart, genN2spart(op(giveSpartSector(spart)))); 
	all_sparts:= [spart, op(smallers)]; 
	#schurs:= map(x-> s[op(x)], all_sparts); 
	schurs_m:= map(x->a[x]*sSchurBar_en_m(all_sparts[x]), [seq(i, i=1..nops(all_sparts))]); 
	schurs_s:= map(x-> sbar[op(x)], all_sparts); 
	preAns:= add( a[k]*schurs_s[k], k=1..nops(all_sparts)); 
	systeq := collect_monomials(m[op(spart)]-add(k, k in schurs_m)); 
	allindets:= solve_monomialeq(systeq); 
	return subs(allindets, preAns); 
end proc:

m_en_sSchurEtoile:= proc(spart)
	option remember;
	local smallers, all_sparts, schurs_m,schurs_s, preAns, systeq, allindets;
	#smallers:= sKeep_smaller_sparts(spart, genN2spart(op(giveSpartSector(spart)))); 
	#all_sparts:= [spart, op(smallers)]; 
	all_sparts:= genN2spart(op(giveSpartSector(spart)));
	#schurs:= map(x-> s[op(x)], all_sparts); 
	schurs_m:= map(x->a[x]*sSchurEtoile_en_m(all_sparts[x]), [seq(i, i=1..nops(all_sparts))]); 
	schurs_s:= map(x-> sEt[op(x)], all_sparts); 
	preAns:= add( a[k]*schurs_s[k], k=1..nops(all_sparts)); 
	systeq := collect_monomials(m[op(spart)]-add(k, k in schurs_m)); 
	allindets:= solve_monomialeq(systeq); 
	return subs(allindets, preAns); 
end proc:

m_en_sSchurBarEtoile:= proc(spart)
	option remember;
	local smallers, all_sparts, schurs_m,schurs_s, preAns, systeq, allindets;
	#smallers:= sKeep_smaller_sparts(spart, genN2spart(op(giveSpartSector(spart)))); 
	#all_sparts:= [spart, op(smallers)]; 
	all_sparts:= genN2spart(op(giveSpartSector(spart)));
	#schurs:= map(x-> s[op(x)], all_sparts); 
	schurs_m:= map(x->a[x]*sSchurBarEtoile_en_m(all_sparts[x]), [seq(i, i=1..nops(all_sparts))]); 
	schurs_s:= map(x-> sbarEt[op(x)], all_sparts); 
	preAns:= add( a[k]*schurs_s[k], k=1..nops(all_sparts)); 
	systeq := collect_monomials(m[op(spart)]-add(k, k in schurs_m)); 
	allindets:= solve_monomialeq(systeq); 
	return subs(allindets, preAns); 
end proc:

SuperConjugate:= proc(spart)
	option remember;
	local nspart, kspart, antiSpart, symSpart, stopdo, col_one, k;
	nspart:= switch_notation(spart);
	nspart:= map(x-> x[1..2], nspart);
	kspart:= nspart;
	antiSpart:= [];
	symSpart:= [];
	stopdo:= nspart[1][1];
	if nspart[1][2] = "C" then stopdo:= stopdo+1; end if;
	for k from 1 to stopdo do
		if kspart[-1][1] = 0 then
			kspart:= kspart[1..-2];
			antiSpart:= [op(antiSpart), nops(kspart)];
			col_one:= [ seq([1,0],j=1..nops(kspart))];
			kspart:= kspart - col_one;
			kspart:= map(x-> if x[1] = 0 and x[2] <> "C" then NULL; else x; end if, kspart);
		else
			col_one:= [ seq([1,0],j=1..nops(kspart))];
			kspart:= kspart - col_one;
			symSpart:= [op(symSpart), nops(kspart)];
			kspart:= map(x-> if x[1] = 0 and x[2] <> "C" then NULL; else x; end if, kspart);
		end if;
	end do:
	return [[],[],antiSpart, symSpart]; 
end proc:

mono_expr_to_schur:= proc(expr_m, theschur)
	option remember;
	local monos, subslist, thetype, expr_s;
	monos:= indets(expr_m, monomial_symbolic); 
	if		theschur = "s" then
		subslist:= map(x-> x = m_en_sSchur([op(x)]), monos);
		thetype:= schur_symbolic;
	elif	theschur = "sbar" then
		subslist:= map(x-> x = m_en_sSchurBar([op(x)]), monos);
		thetype:= schurbar_symbolic;
	elif	theschur = "sEt" then
		subslist:= map(x-> x = m_en_sSchurEtoile([op(x)]), monos);
		thetype:= schurEtoile_symbolic;
	elif	theschur = "sbarEt" then
		subslist:= map(x-> x = m_en_sSchurBarEtoile([op(x)]), monos);
		thetype:= schurbarEtoile_symbolic;
	else
		print("ERROR, wrong second argument", "Choose from s, sbar, sEt, sbarEt"); 
	end if;
	expr_s := subs(subslist, expr_m);
	expr_s := collect_by_type(thetype, expr_s); 
	return expr_s;
end proc:

mono_expr_to_ep:= proc(expr_m)
	option remember;
	local monos, sublist, expr_ep; 
	monos:= indets(expr_m, monomial_symbolic); 
	sublist:= map(x-> x= m_en_ep([op(x)]), monos); 
	expr_ep:= subs(sublist, expr_m); 
	expr_ep:= collect_by_type(ep_symbolic, expr_ep); 
	return expr_ep; 
end proc:

mono_expr_to_e:= proc(expr_m)
	option remember;
	local monos, sublist, expr_ep; 
	monos:= indets(expr_m, monomial_symbolic); 
	sublist:= map(x-> x= m_en_e([op(x)]), monos); 
	expr_ep:= subs(sublist, expr_m); 
	expr_ep:= collect_by_type(elementary_symbolic, expr_ep); 
	return expr_ep; 
end proc:

m_en_ph:= proc(spart)
	local all_sparts, ep_m, ep_ep, preAns, systeq, allindets; 
	option remember;
	all_sparts:= genN2spart(op(giveSpartSector(spart)));
	ep_m:= map(x-> a[x]*ph_expr_to_mono(ph[op(all_sparts[x])]), [seq(i, i=1..nops(all_sparts))]);
	ep_ep:= map(x-> ph[op(x)], all_sparts);
	preAns:= add(a[k]*ep_ep[k], k=1..nops(all_sparts));
	systeq:= collect_monomials(m[op(spart)]- add(k, k in ep_m)); 
	allindets:= solve_monomialeq(systeq);
	return subs(allindets, preAns); 
end proc:

mono_expr_to_ph:= proc(expr_m)
	option remember;
	local monos, sublist, expr_ep; 
	monos:= indets(expr_m, monomial_symbolic); 
	sublist:= map(x-> x= m_en_ph([op(x)]), monos); 
	expr_ep:= subs(sublist, expr_m); 
	expr_ep:= superCollect(expr_ep); 
	return expr_ep; 
end proc:
mono_expr_to_h:= proc(expr_m)
	option remember;
	local monos, sublist, expr_ep; 
	monos:= indets(expr_m, monomial_symbolic); 
	sublist:= map(x-> x= m_en_h([op(x)]), monos); 
	expr_ep:= subs(sublist, expr_m); 
	expr_ep:= collect_by_type(homogeneous_symbolic, expr_ep); 
	return expr_ep; 
end proc:

h_expr_to_mono:= proc(expr_p)
	option remember;
	local eps, sublist, expr_out;
	eps:= indets(expr_p, homogeneous_symbolic); 
	sublist:= map(x-> x = h_en_m([op(x)]), eps);
	expr_out:= subs(sublist, expr_p); 
	expr_out:= collect_monomials(expr_out); 
	return expr_out; 
end proc:

ep_expr_to_mono:= proc(expr_p)
	option remember;
	local eps, sublist, expr_out;
	eps:= indets(expr_p, ep_symbolic); 
	sublist:= map(x-> x = ep_en_m([op(x)]), eps);
	expr_out:= subs(sublist, expr_p); 
	expr_out:= collect_monomials(expr_out); 
	return expr_out; 
end proc:

ph_expr_to_mono:= proc(expr_ph)
	option remember;
	local expr_e, rho_expr_e, expr_mono;
	expr_e := N1convertexpr(subs(ph=e,expr_ph));
	rho_expr_e:= rho_on_expr(expr_e);
	expr_mono:= N2convertexpr(N1LinBaseConvert(rho_expr_e, monomial_symbolic)); 
	return expr_mono;
end proc:

e_expr_to_mono:= proc(expr_p)
	local eps, sublist, expr_out;
	eps:= indets(expr_p, elementary_symbolic); 
	sublist:= map(x-> x = e_en_m([op(x)]), eps);
	expr_out:= subs(sublist, expr_p); 
	expr_out:= collect_monomials(expr_out); 
	return expr_out; 
end proc:

schur_expr_to_mono:= proc(expr_s)
	local schurs, sample_s, sublist, expr_out;
	schurs:= indets(expr_s, superbase);
	sample_s:= schurs[1];
	if		type(sample_s, schur_symbolic) then
		sublist:= map(x-> x = sSchur_en_m([op(x)]), schurs);
	elif	type(sample_s, schurbar_symbolic) then
		sublist:= map(x-> x = sSchurBar_en_m([op(x)]), schurs);
	elif	type(sample_s, schurEtoile_symbolic) then
		sublist:= map(x-> x = sSchurEtoile_en_m([op(x)]), schurs);
	elif	type(sample_s, schurbarEtoile_symbolic) then
		sublist:= map(x-> x = sSchurBarEtoile_en_m([op(x)]), schurs);
	else
		print("ERROR: Wrong type of argument");
		return NULL;
	end if;
	expr_out := subs(sublist, expr_s);
	expr_out := collect_monomials(expr_out); 
	return expr_out;
end proc:

schurLinBaseConvert:= proc(exprin_raw, totype, N1mode:=1)
	local sample, exprin, out;
	if N1mode = 1 then
		exprin := N2convertexpr(exprin_raw);
	else
		exprin := exprin_raw;
	end if;
	sample:= indets(exprin_raw, superbase);

	sample:= sample[1]; 
	if type(sample, monomial_symbolic) then
		out:= mono_expr_to_schur(exprin, totype); 
	elif type(sample, elementary_symbolic) and totype = "p" then
		out:= e2p(exprin); 
	elif totype = "s" or totype = "sbar" or totype= "sbarEt" or totype = "sEt" then
		out:= mono_expr_to_schur(schur_expr_to_mono(exprin), totype); 
	elif totype = "m" then
		out:= schur_expr_to_mono(exprin);
	elif totype = "p" then
		out:= m_to_p(schur_expr_to_mono(exprin)); 
	else
		print("ERROR: supported types (second argument) are s, sbar, sbarEt, sEt, m", "remember to use double quote marks"); 
		return NULL;
	end if;
	if N1mode = 1 then
		return N1convertexpr(out); 
	else 
		return out;
	end if;
end proc:

LinBaseConvert:= proc(exprin_raw, totype, N1mode:=0)
	local expr_in, the_type, expr_mono, expr_out, types;
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
				ph_symbolic
			];
	if super_whattype(exprin_raw) = other then return exprin_raw; end if;
	if N1mode= 1 then
		expr_in:= N2convertexpr(exprin_raw);
	else
		expr_in:= exprin_raw;
	end if;
	if [op([op(indets(expr_in,indexed))][1])] = [[],[],[],[]] then 
		return subs(op(indets(expr_in,indexed))=1, expr_in);
	end if;
	the_type:= super_whattype(expr_in);
	if the_type = totype then return exprin_raw; end if; 
	if the_type = monomial_symbolic then
		expr_mono:= expr_in;
	elif the_type = powersum_symbolic then
		expr_mono:= p_to_m(expr_in);
	elif the_type = homogeneous_symbolic then
		expr_mono:= h_expr_to_mono(expr_in); 
	elif the_type = elementary_symbolic then
		expr_mono:= e2m(expr_in); 
	elif the_type = g_symbolic then
		print("ERROR, not yet defined on gLambda");
		return NULL;
	elif the_type = schur_symbolic then
		expr_mono:= schur_expr_to_mono(expr_in); 
	elif the_type = schurEtoile_symbolic then
		expr_mono:= schur_expr_to_mono(expr_in); 
	elif the_type = schurbar_symbolic then
		expr_mono:= schur_expr_to_mono(expr_in); 
	elif the_type = schurbarEtoile_symbolic then
		expr_mono:= schur_expr_to_mono(expr_in); 
	elif the_type = ep_symbolic then
		expr_mono := ep_expr_to_mono(expr_in);
	elif the_type = ph_symbolic then
		expr_mono := ph_expr_to_mono(expr_in); 
	else 
		print("Supported expr types are", types); 
		return NULL;
	end if;
	if totype = monomial_symbolic then
		expr_out:= expr_mono;
	elif totype = powersum_symbolic then
		expr_out:= superCollect(m_to_p(expr_mono)); 
	elif totype = homogeneous_symbolic then
		expr_out:= superCollect(mono_expr_to_h(expr_mono)); 
	elif totype = elementary_symbolic then
		expr_out:= superCollect(mono_expr_to_e(expr_mono)); 
	elif totype = g_symbolic then
		print("ERROR, not yet defined on gLambda");
		return NULL;
	elif totype = schur_symbolic then
		expr_out:=  mono_expr_to_schur(expr_mono, "s"); 
	elif totype = schurEtoile_symbolic then
		expr_out:=  mono_expr_to_schur(expr_mono, "sEt"); 
	elif totype = schurbar_symbolic then
		expr_out:=  mono_expr_to_schur(expr_mono, "sbar"); 
	elif totype = schurbarEtoile_symbolic then
		expr_out:=  mono_expr_to_schur(expr_mono, "sbarEt"); 
	elif totype = ep_symbolic then
		expr_out:=  mono_expr_to_ep(expr_mono);
	elif totype = ph_symbolic then
		expr_out:=  mono_expr_to_ph(expr_mono);
	else
		print("Supported out types are", types); 
		return NULL;
	end if;
	if N1mode = 1 then 
		return N1convertexpr(expr_out);
	else
		return expr_out; 
	end if;
end proc:

N1LinBaseConvert:= proc(expr, totype)
	return LinBaseConvert(expr, totype, 1); 
end proc:

superCollect:= proc(expr)
	if super_whattype(expr) = other then return expr; end if;
	return collect_by_type(super_whattype(expr), expr); 
end proc:

N1superCollect:= proc(expr)
	return N1convertexpr(superCollect(N2convertexpr(expr))); 
end proc:
##############################################################
N1omega_monomial:= proc(expr)
	local N2expr;
	N2expr:= N2convertexpr(expr); 
	return N1convertexpr(collect_monomials(subs(alpha=1, monomial_omega_alpha(N2expr)))); 
end proc:

rhoAct_one_powersum:= proc(spart)
	local the_sign;
	the_sign:= (-1)^(add(k, k in Flatten(spart)) + nops(spart[4]));
	return the_sign*ep[op(spart)]; 
end proc:

rhoAct_expr_powersum:= proc(N1expr)
	local expr, powersums, sublist, out;
	expr:= N2convertexpr(N1expr); 
	powersums:= indets(expr, powersum_symbolic);
	sublist:= map(x-> x = rhoAct_one_powersum([op(x)]), powersums); 
	out:= superCollect(subs(sublist, expr)); 
	out:= N1convertexpr(out);
	return out;
end proc:

rho_on_expr:= proc(N1expr)
	local thetype, expr_p, rho_expr_p;
	thetype:= super_whattype(N2convertexpr(N1expr)); 
	expr_p:= N1LinBaseConvert(N1expr, powersum_symbolic);
	rho_expr_p:= rhoAct_expr_powersum(expr_p);
	return N1LinBaseConvert(rho_expr_p, thetype); 
end proc:

omega_on_expr:= proc(N1expr)
	local thetype, expr_p, expr_m, omega_expr;
	thetype:= super_whattype(N2convertexpr(N1expr)); 
	expr_m:= N1LinBaseConvert(N1expr, monomial_symbolic);
	omega_expr:= N1omega_monomial(expr_m);
	return N1LinBaseConvert(omega_expr, thetype); 
end proc:

rhoDash_on_ph:= proc(N1spart)
	local N2spart, sparts, N1sparts, monos, rho_omega_monos, theH_in_m, the_prods, Eexpand;
	N2spart:= [[],[],op(N1spart)];
	sparts:= genN2spart(op(giveSpartSector(N2spart)));
	N1sparts:= map(x-> [x[3],x[4]], sparts);
	monos:= map(x-> m[op(x)], N1sparts);
	rho_omega_monos:= map(x-> rho_on_expr(omega_on_expr(x)), monos); 
	theH_in_m:= LinBaseConvert(ph[op(N2spart)], monomial_symbolic);
	the_prods:=map(x->monomial_scalar_prod(theH_in_m, N2convertexpr(x), 1), rho_omega_monos); 
	the_prods:= map(factor, the_prods);
	Eexpand:= add( the_prods[k]*e[op(N1sparts[k])], k=1..nops(N1sparts)); 
	return Eexpand; 
end proc:

rhoDash_on_ph_expr:= proc(expr_ph)
	local phs, rhoDash_phs;
	phs:= indets(expr_ph, ph_symbolic); 
	rhoDash_phs:= map(x->x=rhoDash_on_ph([op(x)]), phs);
	return superCollect(subs(rhoDash_phs, expr_ph));
end proc:

rhoDash:= proc(expr)
	local thetype, expr_ph, rhoDashexprph;
	thetype:= super_whattype(expr);
	expr_ph:=N1LinBaseConvert(expr, ph_symbolic);
	rhoDashexprph:= rhoDash_on_ph_expr(expr_ph);
	return N1LinBaseConvert(rhoDashexprph,thetype);
end proc:

phiDash:= proc(expr)
	return rhoDash(omega_on_expr(expr));
end proc:

mphiDash:= proc(expr)
	return omega_on_expr(rhoDash(expr)); 
end proc:

giveOnAllBasis:= proc(expr,give_ans:=0, with_Schur:=0)
	local types, allexpr, k:
	types:= [
				powersum_symbolic, 
				monomial_symbolic, 
				homogeneous_symbolic, 
				elementary_symbolic, 
				#schur_symbolic, 
				#schurEtoile_symbolic, 
				#schurbar_symbolic, 
				#schurbarEtoile_symbolic, 
				ep_symbolic,
				ph_symbolic
			];
	allexpr:= map(x-> N1LinBaseConvert(expr, x), types);
	for k in allexpr do
		print(k);
	end do:
	if give_ans = 1 then return allexpr: end if;
end proc:

boson_diff:= proc(n,one_term, basis, timesn:=1)
	local spart, zeds, num, position, newzeds;
	spart:= [op(one_term)];
	if add(k, k in Flatten(spart)) < n then return 0; end if;
	zeds:= spart[2];
	num:= Occurrences(n, zeds);
	if num = 0 then return 0; end if;
	position:= Search(n, zeds);
	newzeds:= subsop(position = NULL, zeds);
	return n*num*basis[spart[1], newzeds];
end proc:

boson_diff_expr:= proc(n, expr, basis)
	local expr_in, terms, sublist, out;
	expr_in:= N1superCollect(expr);
	terms:= indets(expr_in, superbase);
	sublist:= map(x-> x=boson_diff(n,x,basis), terms);
	out:= subs(sublist,expr_in);
	#out:= subs(basis[[],[]] = 1, out);
	return N1superCollect(out);
end proc:

boson_diff_list_expr:= proc(the_seq, expr, basis)
	local the_expr,k;
	the_expr:= expr;
	for k in the_seq do
		the_expr := N1superCollect(boson_diff_expr(k, the_expr, basis));
	end do:
	return the_expr;
end proc:

fermion_diff:= proc(n, expr, basis)
	local spart, position, newspart, fpart;
	spart:=[op(expr)];
	fpart:= spart[1];
	position:= Search(n,fpart);
	if position = 0 then return 0; end if;
	newspart:= [subsop(position=NULL,fpart), spart[2]];
	return (-1)^(position+1)*basis[op(newspart)];
end proc:

fermion_diff_expr:= proc(n, expr, basis)
	local expr_in, terms, sublist, out;
	expr_in:= N1superCollect(expr);
	terms:= indets(expr_in, superbase);
	sublist:= map(x-> x=fermion_diff(n,x,basis), terms);
	out:= subs(sublist,expr_in);
	#out:= subs(basis[[],[]] = 1, out);
	return N1superCollect(out);
end proc:

fermion_diff_list_expr:= proc(the_seq, expr, basis)
	local the_expr,k;
	the_expr:= expr;
	for k in the_seq do
		the_expr := N1superCollect(fermion_diff_expr(k, the_expr, basis));
	end do:
	return the_expr;
end proc:

one_e_dash_n:= proc(n,expr_p)
	local el_en_p, powersums, coeffp, sparts, action, result, aterm;
	aterm:= indets(expr_p, indexed);
	if nops(aterm) = 0 then return 0; end if;
	if type(aterm[1], powersum_symbolic) = false then return 0; end if;
	el_en_p:= N1LinBaseConvert(e[[],[n]], powersum_symbolic);
	powersums:= [op(indets(el_en_p, powersum_symbolic))];
	coeffp:= map(x-> coeff(el_en_p,x), powersums);
	sparts:= map(x-> [op(x)], powersums);
	action:= map(x-> boson_diff_list_expr(x[2],expr_p,p), sparts);
	result:= add( coeffp[k]*action[k], k=1..nops(coeffp)); 
	return N1superCollect(result);
end proc:
one_h_dash_n:= proc(n, expr_p)
	local el_en_p, powersums, coeffp, sparts, action, result, aterm;
	aterm:= indets(expr_p, indexed);
	if nops(aterm) = 0 then return 0; end if;
	if type(aterm[1], powersum_symbolic) = false then return 0; end if;
	el_en_p:= N1LinBaseConvert(h[[],[n]], powersum_symbolic);
	powersums:= [op(indets(el_en_p, powersum_symbolic))];
	coeffp:= map(x-> coeff(el_en_p,x), powersums);
	sparts:= map(x-> [op(x)], powersums);
	action:= map(x-> boson_diff_list_expr(x[2],expr_p,p), sparts);
	result:= add( coeffp[k]*action[k], k=1..nops(coeffp)); 
	return N1superCollect(result);
end proc:

hdash_n:= proc(n, expr)
	local thetype, expr_p, hdashp;
	if n = 0 then return expr; end if; 
	if n < 0 then return 0; end if; 
	thetype:= super_whattype(expr);
	expr_p:= N1LinBaseConvert(expr, powersum_symbolic);
	hdashp:=one_h_dash_n(n, expr_p);
	return N1LinBaseConvert(hdashp, thetype);
end proc:

edash_n:= proc(n, expr)
	local thetype, expr_p, edashp;
	if n = 0 then return expr; end if; 
	if n < 0 then return 0; end if; 
	thetype:= super_whattype(expr);
	expr_p:= N1LinBaseConvert(expr, powersum_symbolic);
	edashp:=one_e_dash_n(n, expr_p);
	return N1LinBaseConvert(edashp, thetype);
end proc:

## Prendre code Olivier ##
del_etilde_n:=proc(n, expr)
	local out;
	out:= N1LinBaseConvert(expr, elementary_symbolic);
	out:= fermion_diff_expr(n,out,e);
	out:= N1LinBaseConvert(out, super_whattype(expr));
	return out;
end proc:

BGamma_1_n:=proc(n, expr)
	local terms, sparts, max_ell, r, thetype, out, er_expr, es_er_expr, eexpr_m, hs_m, hs_es_er_expr, s, newterm;
#Ne respecte pas le secteur, debugger dans les boucles. OK
	terms:= indets(expr, superbase); 
	thetype:= super_whattype(terms[1]);
	sparts:= map(x-> [op(x)], terms); 
	max_ell:= max(map(x-> nops(Flatten(x)), sparts));
	out:=0;
	for r from 0 to max_ell do
		print("er_expr to go on", expr, r, "over ", max_ell); 
		er_expr:= edash_n(r, expr);
		#print(1,er_expr); 
		if er_expr <> 0 then
		for s from (n+r) to n+r+max_ell do
			print("s-n-r", s-n-r, er_expr);
			es_er_expr:= edash_n(s-n-r, er_expr);
			if es_er_expr = 0 then break; end if;
			#print(2, es_er_expr); 
			eexpr_m:= N1LinBaseConvert(es_er_expr, monomial_symbolic); 
			#print(3, eexpr_m); 
			#print(h[[s],[]]);
			#print(es_er_expr); 
			hs_m:= N1LinBaseConvert(h[[s],[]], monomial_symbolic); 
			#print(4,hs_m); 
			hs_es_er_expr:= (-1)^(r+s)*expr_mono_prod( N2convertexpr(hs_m), N2convertexpr(eexpr_m));
			#print(hs_es_er_expr);
			hs_es_er_expr:= N1convertexpr(hs_es_er_expr); 
			#print(5, hs_es_er_expr); 
			newterm:= N1LinBaseConvert(hs_es_er_expr, thetype);
			print("term just generate",newterm);
			out:= newterm + out;
			print("new result (newterm + last term)", out);
			#print(6, out, "out"); 
		end do:
		end if:
	end do:
	return superCollect((-1)^n*out); 
end proc:

FGamma_n:= proc(n, expr)
	local terms, thetype, sparts, thedeg, out, hda_rn, thee, res, r;
	terms:= indets(expr, superbase);
	if nops(terms) = 0 then 
		thedeg:=0;
	else
		thetype:= super_whattype(terms[1]);
		sparts:= map(x-> [op(x)], terms);
		thedeg:= add(k, k in Flatten(sparts[1]));
	end if;
	out:=0;
	for r from 0 to thedeg do
		hda_rn:= N1LinBaseConvert(hdash_n(r, expr), monomial_symbolic);
		if hda_rn =0 then break; end if;
		thee:= N1LinBaseConvert(e[[r+n],[]], monomial_symbolic);
		res:= N1convertexpr(expr_mono_prod(N2convertexpr(thee), N2convertexpr(hda_rn)));
		out:= superCollect(out + (-1)^(r)*res); 
	end do:
	out := N1LinBaseConvert(out, thetype); 
	return out;
end proc:


#### NS Macdo #####
nsMacdo:= proc(eta)
#Broken
	local smallercomps, preMacdo, eigenVals, YiEs, systEq, soln,N, vars, out;
	smallercomps:= give_smallerComps(eta);
	N:= nops(eta);
	vars:= {seq(z||k, k=1..N)};
	preMacdo:= nsMonome(eta) + add( a[x]*nsMonome(smallercomps[x]), x=1..nops(smallercomps)); 
	eigenVals:=		map(i->eigen_val_opYi(i, eta)*preMacdo, [seq(k, k=1..N)]); 
	YiEs:=			map(i->opYi(i,preMacdo,N), [seq(k, k=1..N)]); 
	systEq:= eigenVals-YiEs;
	systEq:=map(x-> Coefficients(x, vars), systEq);
	#systEq:= map(x-> (collect(simplify(x), [seq(z||k, k=1..N)], 'distributed')), systEq); 
	soln:= solve(systEq, indets(preMacdo, a_indet)); 
	out:= subs(soln, preMacdo); 
	#return [soln, preMacdo];
	return out;
end proc:

###### Macdo ######
stdMacdo:= proc(part)
	local nbVars, ns_mac, mac, comp;
	comp:= ListTools:-Reverse(part);
	nbVars:= add(k, k in part); 
	if nops(comp) < nbVars then comp:= [seq(0, k=1..(nbVars-nops(comp))), op(comp)]; end if; 
	ns_mac:= nsMacdo(comp);
	mac:= tSymmetrize(ns_mac, nbVars); 
	print("tSymmetrized");
	mac:= z_to_m(mac); 
	mac:= collect_monomials(mac, m[[],[],[],[op(part)]]); 
	return mac;
end proc:

sMacdo_NS:= proc(spart, mode:=3)
	local stdL, stL, sdL, sLs, nbVars, ell_lambda, ns_mac, mac, N, mbarbar, mbar, mubar, bigM, comp, sector, super_mono, k;
	stdL:= ListTools:-Reverse(spart[1]);
	mbarbar:= nops(stdL);
	stL:= ListTools:-Reverse(spart[2]);
	mbar:= nops(stL);
	sdL:= ListTools:-Reverse(spart[3]);
	mubar:= nops(sdL);
	sLs:= ListTools:-Reverse(spart[4]);
	bigM:= mbar+mubar+mbarbar;
	nbVars := max( map(x-> nops(Flatten(x)), genN2spart(op(giveSpartSector(spart))))); 
	N:= nbVars; 
	ell_lambda:= nops(Flatten(spart));
	if ell_lambda < nbVars then 
		comp:= [op(stdL), op(stL), op(sdL), op(sLs), seq(0, k=1..(nbVars-ell_lambda))]; 
	else 
		comp:= [op(stdL), op(stL), op(sdL),  op(sLs)]; 
	end if; 
	ns_mac:= nsMacdo(comp);
	sector:= giveSpartSector(spart);
	bigM:= sector[2]+sector[3] + sector[4];
	mac:= tSymmetrize(ns_mac,nbVars,bigM+1,nbVars); 
	if mubar > 1 then
		if mode <> 3 then mac:= AntiSymetrize(mac, [seq(k+mbarbar+mbar, k=1..mubar)]); end if;
		if mode = 3 then mac:= tantiSymmetrize(mac, nbVars, mbarbar+mbar+1, mbarbar+mbar+mubar); end if;
	end if;
	if mbar > 1 then
		if mode <> 3 then mac:= AntiSymetrize(mac, [seq(k+mbarbar, k=1..mbar)]);end if;
		if mode = 3 then mac:= tantiSymmetrize(mac, nbVars, mbarbar+1, mbarbar+mbar); end if;
	end if;
	if mbarbar > 1 then
		if mode = 1 then	mac:= Var_Symmetrize(mac, [seq(k, k=1..mbarbar)]); end if;
		if mode = 3 then	mac:= tSymmetrize(mac, mbarbar-1); print(mode, "engaged");  end if;
	end if;
	super_mono:=1;
	for k from 1 to bigM do
		if k <= mbarbar then super_mono:= phi||k*theta||k*super_mono; end if;
		if k > mbarbar and k <= mbar+mbarbar then super_mono:= phi||k*super_mono; end if;
		if k > mbarbar+mbar then super_mono:= theta||k*super_mono; end if;
	end do:
	mac:= super_mono*mac;
	#mac:= Kw(mac, nbVars); 
	#last_sym:= SNcheckCoxeter(mbarbar, mbar, mubar, N); 
	#mac:= add(apply_sigma_si(mac, last_sym[k]), k=1..nops(last_sym)); 
	#perm_mac:= map(x->apply_sigma_si(mac,x), last_sym); 
	mac:= Kw(mac, N); 
	#permutations:= permute(4);
	#permuations:= subs([1,2,4,3]=NULL, permutations); 
	#mac:=add(k, k in map(x-> Ksigma_j(mac,x), permutations)); 
	#mac:= add(k, k in perm_mac); 
	mac:= z_to_m(mac); 
	mac:= collect_monomials(mac, m[op(spart)]); 
	return mac;
end proc:

get_h:= proc(spart)
	local sector, sparts, sample, eq1, eqs, systeq, soln;
	sector:= giveSpartSector(spart);
	sparts:= genN2spart(op(sector)); 
	sample:= add( a[k]*m[op(sparts[k])], k=1..nops(sparts));
	eq1:= monomial_scalar_prod(m[op(spart)], sample, 1) - 1;
	eqs:= map(x-> monomial_scalar_prod(sample,m[op(x)],1), subs(spart=NULL, sparts)); 
	systeq:= [eq1, op(eqs)]; 
	soln:=solve(systeq, indets(sample, a_indet));
	return collect_monomials(subs(soln, sample)); 
end proc:

N2m_to_h:= proc(spart)
	local sector, sparts, homos, homos_rep, lin_comb, systeq; option remember;
	sector:= giveSpartSector(spart); 
	sparts:= genN2spart(op(sector)); 
	homos:= map(x-> get_h(x), sparts); 
	homos_rep:= add(a[k]*h[sparts[k]], k=1..nops(sparts)); 
	lin_comb:= add(a[k]*homos[k], k=1..nops(sparts)); 
	systeq:= m_systeq(m[op(spart)] - lin_comb); 
	return subs(solve(systeq), homos_rep);
end proc:

linN2m2h:= proc(expr)
	local monos, sublist;
	monos:= indets(expr, monomial_symbolic); 
	sublist:= map(x-> x = N2m_to_h([op(x)]), monos);
	return superCollect(subs(sublist, expr)); 
end proc:

exp_fns_Jack:= proc(spart::pN2spart,sym:="SAAS", in_alpha:=1) 
local thesector, longest_spart, phis, thetas, zeds, scomposition, thensJack, superJack, pts, mbarbar, mbar, mubar;
option remember;
	#Slow#
	#Generates the superJack N=2 using the non-symmetric Jack method (Slow)
	thesector:=giveSpartSector(spart);
	longest_spart:=max(map(x-> nops(Flatten(x)), genN2spart(op(thesector))));
	pts:= spart[1];
	phis:= spart[2];
	thetas:= spart[3];
	zeds:= spart[4]; 
	mbarbar:= nops(pts);
	mbar:= nops(phis);
	mubar:= nops(thetas);
	if sym = "SAAS" then
			scomposition:= [op(Reverse(pts)),op(Reverse(phis)), op(Reverse(thetas)), op(Reverse(zeds))]; 
	#elif sym = "SAAS2" then
			#scomposition:= [op(Reverse(pts)), op(Reverse(thetas)),op(Reverse(phis)), op(Reverse(zeds))]; 
	elif sym = "AASS" then
			scomposition:= [op(Reverse(phis)), op(Reverse(thetas)),op(Reverse(pts)), op(Reverse(zeds))]; 
	end if;
	#scomposition:= [op(pts),op(phis), op(thetas), op(zeds)]; 
	if longest_spart > nops(scomposition) then
		scomposition:= [op(scomposition), seq(0, k=1..(longest_spart -nops(scomposition)))];
	end if;
	thensJack:= nsJack(scomposition);
	#thensJack:= Var_Symmetrize(thensJack, [seq(k, k=1..mbarbar)]);
	#thensJack:= AntiSymetrize(thensJack, [ seq(k+mbarbar, k=1..mbar)]);
	#thensJack:= AntiSymetrize(thensJack, [ seq(k+mbarbar + mbar, k=1..mubar) ]);
	if sym = "SAAS" then
		thensJack:= mul(phi||k*theta||k, k=1..mbarbar)*mul(phi||(k+mbarbar), k=1..mbar)*mul(theta||(k+mbarbar+mbar), k=1..mubar)*thensJack;
	elif sym = "AASS" then
		thensJack:= mul(phi||(k), k=1..mbar)*mul(theta||(k+mbar), k=1..mubar)*mul(phi||(k+mbar+mubar)*theta||(k+mbar+mubar), k=1..mbarbar)*thensJack;
	end if;

	superJack:= Kw(thensJack, longest_spart); 
	if in_alpha <> 0 then superJack:= subs(beta=1/alpha, superJack); end if;
	superJack:= collect_monomials(z_to_m(superJack), m[op(spart)]); 
	return superJack; 
end proc:

check_norms:= proc(sector, mode)
	local Jacks, sparts, norms, calc, rel;
	Jacks:= sJack_sector(op(sector), mode); 
	sparts:= map(x-> give_greatest_monomial(x, mode), Jacks);
	sparts:= map(x-> [op(x)], sparts); 
	norms:= map(x-> monomial_scalar_prod(x,x), Jacks); 
	calc:= map(x-> Jack_norm(x, mode), sparts); 
	rel := zip((x,y)-> factor(x/y), norms, calc); 
	return rel; 
end proc:

check_specialize:= proc(sector, VARS:=0)
	local sparts, nb_var, Jacks,specs, calc, rati, spart_rati;
	Jacks:= sJack_sector(op(sector)); 
	if VARS <> 0 then
		Jacks:= map(x-> if nops(Flatten([op(give_greatest_monomial(x))])) > VARS then NULL; else x; end if, Jacks); 
	end if;
	sparts:= map(x-> [op(give_greatest_monomial(x))], Jacks);
	if VARS=0 then
		nb_var:= map(x-> nops(Flatten(x)), sparts);
		nb_var:= max(nb_var); 
	else
		nb_var:=VARS;
	end if;
	calc:= map(x-> calc_specialize_E(x, nb_var), sparts); 
	specs:= map(x-> specialize_E(x, nb_var), Jacks);
	rati:= zip((x,y)-> factor(x/y), specs, calc); 
	spart_rati:= zip((x,y)-> [x,y], sparts, rati); 
	return spart_rati; 
end proc:

calc_specialize_E:= proc(spart, nb_var, mode:=[1,2,3])
	local sector, mbar, mubar, minimal_triangle, trig_part, delta, quatuor, M3, spart3, sp3_indices, DeltaSpart_ind, num_terms, var_co, the_num, the_denom, mbarbar, plus_factor, pairs, sparts, new_pol;
	sector:= giveSpartSector(spart); 
	quatuor := star_quatuor(spart, mode);
	M3:= spart_sector[2] + spart_sector[3] + spart_sector[4]; 
	spart3:= quatuor[4];
	##
	mbar:=	sector[2];
	mubar:= sector[3];
	mbarbar:= sector[4];
	##
	minimal_triangle:= [seq(k, k=1..mbar), seq(l, l=1..mubar)]; 
	trig_part:= sort(minimal_triangle, `>`); 
	#lnmm:= sector[1] - add(k, k in trig_part); 
	delta:= [seq(seq([i,j], j=1..trig_part[i]), i=1..nops(trig_part ))]; 
	###
	sp3_indices:= [seq(seq([i,j], j=1..spart3[i]), i=1..nops(spart3))];
	DeltaSpart_ind:= map(x-> if x in delta then NULL; else x; end if, sp3_indices); 
	num_terms:= map(x-> nb_var - co_leg_part(op(x), spart3) + alpha*co_arm_part(op(x), spart3), DeltaSpart_ind); 
	plus_factor:= binomial(nb_var-mbar-mubar, mbarbar); 
	the_num:= mul(x, x in num_terms); 
	the_denom:= plus_factor*down_hook(spart, mode); 
	print("factor", plus_factor); 
	return factor(the_num/the_denom); 
end proc:

specialize_E:= proc(pol, nb_var)
	local sector, mbarbar, mbar, mubar, seqbar, ijbar, sequbar, ijubar, ij, vandermonde, pol_in_z, Dpol_in_z, k, pre_spec, sublist, result, new_pol, sparts, pairs;
	#Tester l'évaluation
	#Voir si ca marche avec la formule ... 
	#Arranger pour que ca marche avec les differentes facons de symmetriser
	sector:= givePolySector(pol); 
	mbarbar:= sector[4];
	mbar:=	sector[2];
	mubar:= sector[3];
	#Possible problem with the fact the M_i changes from a symmetrization to the other... 
	#I expect only a sign difference, so I won't code it at first. 
	seqbar:= [seq(k, k=(mbarbar+1)..(mbarbar+mbar))];
	pairs:= choose(seqbar, 2); 
	ijbar:= map(x-> if x[1]<x[2] then x; else NULL; end if, pairs); 
	#ijbar:= map(i-> map(j-> if i < j then [i,j]; else NULL; end if, seqbar ), seqbar); 
	sequbar:= [seq(k, k=(mbarbar+mbar+1)..(mbarbar+mubar+mbar))];
	pairs:= choose(sequbar, 2); 
	ijubar:= map(x-> if x[1]<x[2] then x; else NULL; end if, pairs); 
	ij:= [op(ijbar), op(ijubar)]; 
	ij:= map(x-> if x <> [] then x; else NULL; end if, ij); 
	vandermonde := map(x->z||(x[1]) - z||(x[2]),ij);
	vandermonde := mul(x, x in vandermonde); 
	## maping to 0 monomials that requires too many variables
	sparts:= genN2spart(op(sector));
	sublist:= map(x->if nops(Flatten(x))>nb_var then m[op(x)] = 0; else NULL; end if, sparts); 
	new_pol:= subs(sublist, pol); 
	#####
	pol_in_z:= m2n_expr(new_pol, nb_var);
	Dpol_in_z:= pol_in_z;
	for k in Reverse(sequbar) do
		Dpol_in_z := diff(Dpol_in_z, theta||k);
	end do:
	for k in Reverse(seqbar) do
		Dpol_in_z := diff(Dpol_in_z, phi||k);
	end do:
	for k from 1 to mbarbar do
		Dpol_in_z := diff(diff(Dpol_in_z, theta||k), phi||k); 
	end do:
	pre_spec := simplify(Dpol_in_z/vandermonde);
	#print(pre_spec); 
	#return(vandermonde); 
	sublist:= {seq(z||k = 1, k=1..nb_var)};
	result:= subs(sublist, pre_spec); 
	result:= factor(result); 
	return result;
end proc:


m2n_expr:= proc(expr, nbvar)
	local monos, monos_z, expr_out;
	monos:= indets(expr, monomial_symbolic); 
	monos_z := map(x-> x = m_in_z([op(x)], nbvar), monos); 
	expr_out:= subs(monos_z, expr); 
	return expr_out;
end proc:

N2omega_alpha_p_lambda:= proc(p_Lambda::powersum_symbolic)
	local Lambda, out, enn, ell;
	Lambda := [op(p_Lambda)];
	enn:= add(k, k in Flatten(Lambda)); 
	ell:= add(k, k in map(x-> nops(Lambda[x]), [1,2,3,4])); 
	out:= p_Lambda = (alpha)^(ell)*(-1)^(enn -nops(Lambda[4]))*p_Lambda;
	return out;
end proc:

N2omega_alpha_p_expr:= proc(expr_p)
	local powersums, sublist;
	powersums:= indets(expr_p, powersum_symbolic); 
	sublist:= map(x-> N2omega_alpha_p_lambda(x), powersums);
	return subs(sublist, expr_p); 
end proc:

N2omega_m:= proc(expr_m)
	local expr_p, wexpr_p, wexpr_m;
	expr_p := LinBaseConvert(expr_m, powersum_symbolic); 
	wexpr_p:= N2omega_alpha_p_expr(expr_p); 
	wexpr_m:= LinBaseConvert(wexpr_p, monomial_symbolic); 
	return collect_monomials(wexpr_m); 
end proc:

m_expr_to_jacks:= proc(expr_m)
	local sector, jacks_m, jacks_P, eq, soln, all_jacks, expr_P;
	sector:= givePolySector(expr_m);
	jacks_m:= sJack_sector(op(sector));
	jacks_P:= map(x->P[op(give_greatest_monomial(x))], jacks_m);
	expr_P := add(a[k]*jacks_P[k], k=1..nops(jacks_P)); 
	all_jacks:= add(a[k]*jacks_m[k], k in [seq(l, l=1..nops(jacks_m))]);
	eq:= collect_monomials(expr_m - all_jacks); 
	soln:= solve_monomialeq(eq); 
	return superCollect(subs(soln, expr_P)); 
end proc:
