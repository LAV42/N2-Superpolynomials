#
# Functions related to the CMS model or Cherednik operators 
#
###################
#list of functions#
###################
#		Hpoly:=proc(poly) 
#		Dunkl_i_n:= proc(i, n, poly, Nin:=0, parameter:= beta)
#		H_n:= proc(n, poly, giveinm:=1)
#		I_k_n:= proc(k, n, poly, giveinm:=1)
#		EigenCMSn:= proc(spart,n, hn:=0, IorNot:=NULL, minN:=NULL)
#		lambdabar_i:= proc(composition, i, N)
#		FermDunkl_i_n:= proc(i,n, poly)
#		Itilde_k_n:= proc(k, n, poly, giveinm:=1)




HcmsPolyM:= proc(expr_in_m)
	return z_to_m(sort(expand(Hpoly(old_LinBaseConvert(expr_in_m, `z`))))); 
end proc:
part_Hpoly:= proc(poly, i, nbvars)
	local j, term2, term3, terms, term23;
	terms:= [seq(k, k=(i+1)..nbvars)];
	#for j from i+1 to nbvars do
	#if j > i  then 
	term2:=0; term3:=0;
		term2:=map(j->(((z||i+z||j)/(z||i-z||j)*(z||i*diff(
			poly,z||i)-z||j*diff(poly,z||j)))), terms);
		term3:=map(j->(((z||i*z||j)/((z||i-z||j)^2)*(
				poly-subs({theta||i=theta||j,
				theta||j=theta||i,phi||i=phi||j,
				phi||j=phi||i},poly)))), terms) ;
	#end if;
	#end do:
	term23:= term2 -2*term3;
	return sort(expand(add(k, k in term23)));
end proc:
Hpoly:=proc(poly) 
	local H_on_poly, term1, term23, term3, i,j, Vars, nbvars, varsindices;
	#Hamiltonian as a direct generalization of K_ij
	#The code is pretty much self-explainatory
    	Vars:=giveVars(poly);
    	nbvars:= max(nops(Vars[1]), nops(Vars[2]), nops(Vars[3]));

	term1:=0; term23:=0; term3:=0;
	varsindices:= [seq(k, k=1..nbvars)];
	#term1:=term1+sort(expand(z||i*(diff(z||i*diff(poly,z||i),z||i))));
	term1:= map(x-> z||x*(diff(z||x*diff(poly, z||x), z||x)), varsindices);
	term1:= sort(expand(add(k, k in term1)));
	term23:= map(x-> part_Hpoly(poly,x,nbvars), varsindices);
	term23:= sort(expand(beta*add(k, k in term23)));
	H_on_poly:= sort(expand(term1+term23));
	#H_on_poly:= z_to_m(H_on_poly); 
	return factor(H_on_poly);
end proc:

mH_n:= proc(n, poly_in_m)
	return H_n(n,old_LinBaseConvert(poly_in_m, 'z'), 1);
end proc:

H_n:= proc(n, poly, giveinm:=1)
    local Hpoly, N, Vars;
	# The hamiltonian tower in terms of the sum of the dunkl on every variables
    Vars:= giveVars(poly);
	N:= max(nops(Vars[1]), nops(Vars[2]), nops(Vars[3]));
	if N = 1 then N:= 2; end if;
    Hpoly:= simplify(add(Dunkl_i_n(i, n, poly, N), i=1..N));
    if giveinm = 1 then Hpoly:= z_to_m(Hpoly); end if; 
    return Hpoly;
end proc:
#J_n:= proc(n, poly, giveninm:=1)
    #local Hpoly, N, Vars;
	# The hamiltonian tower in terms of the sum of the dunkl on every variables
    #Vars:= giveVars(poly);
	#N:= max(nops(Vars[1]), nops(Vars[2]), nops(Vars[3]));
	#if N = 1 then N:= 2; end if;
    #Hpoly:= add(Dunkl_i_n(i, n, phi||i*theta||i*diff(diff(poly, phi||i), theta||i), N), i=1..N);
    #if giveinm = 1 then Hpoly:= z_to_m(Hpoly); end if; 
    #return Hpoly;
#end proc:
#H_n:= proc(n, poly, giveinm:=1)
	#local Hpoly, N, Vars; 
	#Vars:= giveVars(poly);
	#N:= max(nops(Vars[1]), nops(Vars[2]), nops(Vars[3]));
	#if N = 1 then N:= 2; end if;
    	#Hpoly:= add(FermDunkl_i_n(i, n, poly), i=1..N);
    	#if giveinm = 1 then Hpoly:= z_to_m(Hpoly); end if; 
    	#return Hpoly;
#end proc:
project_var_sector:= proc(poly_z,var, sector)
	local mbarbar, mbar, Ppoly, k,j, mubar, ind, thevar;
	mbarbar:= sector[4];
	mubar:= sector[3];
	#print(mubar);
	mbar := sector[2];
	Ppoly:= poly_z;
	if var = "pt" then
		for k from 1 to mbarbar do
			Ppoly:= sort(expand(phi||k*theta||k*diff(diff(Ppoly, phi||k), theta||k)));
		end do:
	elif var = "p" then 
		for j from 1 to mbar do
			k:= j+ mbarbar;
			Ppoly:= sort(expand(phi||k*diff(Ppoly, phi||k)));
		end do:
	elif var = "t" then
		for j from 1 to mubar do
			k:= j + mbarbar+mbar;
			Ppoly:= sort(expand(theta||k*diff(Ppoly, theta||k)));
		end do:
	else return NULL;
	end if;
	return Ppoly;
end proc:

expI_n:= proc(smalli,n, poly_in_m)
	local sector, mbarbar, mbar, nbVars, Ipoly, theIndex, mubar, bigM;
	print(poly_in_m);
	sector:= givePolySector(poly_in_m);
	mbarbar:= sector[4];
	mbar:= sector[2];
	mubar:= sector[3];
	bigM:= [0,sector[4], sector[4]+sector[2], sector[4]+sector[3]+sector[2]];
    nbVars:= max(map(x-> nops(Flatten(x)), genN2spart(op(sector))));
	Ipoly:= old_LinBaseConvert(poly_in_m, 'z'); 
	Ipoly:= project_var_sector(Ipoly, "pt", sector); 
	Ipoly:= project_var_sector(Ipoly, "p", sector); 
	Ipoly:= project_var_sector(Ipoly, "t", sector); 
	Ipoly:= Dunkl_i_n(bigM[smalli]+1,n,Ipoly, nbVars); 
	Ipoly:= factor(Kw(Ipoly, nbVars)); 
	Ipoly:= z_to_m(Ipoly);
	return Ipoly;
end proc:
Ibarbar_n:= proc(n,poly_in_m)
	local sector, mbarbar, nbVars, Ipoly;
	sector:= givePolySector(poly_in_m);
	mbarbar:= sector[4];
	nbVars:= max(map(x-> nops(Flatten(x)), genN2spart(op(sector))));
	Ipoly:= old_LinBaseConvert(poly_in_m, 'z'); 
	if mbarbar = 0 then return 0; end if;
	Ipoly:= phi1*theta1*diff(diff(Ipoly, phi1), theta1);
	Ipoly:= Dunkl_i_n(1,n,Ipoly, nbVars);
	Ipoly:= factor(Kw(Ipoly, nbVars)); 
	Ipoly:= z_to_m(Ipoly);
	return Ipoly;
end proc:

Ibar_n:= proc(n, poly_in_m)
	local sector, mbarbar, mbar, nbVars, Ipoly, theIndex;
	sector:= givePolySector(poly_in_m);
	mbarbar:= sector[4];
	mbar := sector[2];
        nbVars:= max(map(x-> nops(Flatten(x)), genN2spart(op(sector))));
	Ipoly:= old_LinBaseConvert(poly_in_m, 'z'); 
	Ipoly:= project_var_sector(Ipoly, "pt", sector); 
	if mbar = 0 then return 0; end if;
	theIndex:= mbarbar+1;
	Ipoly:= phi||theIndex*diff(Ipoly, phi||theIndex);
	Ipoly:= Dunkl_i_n(theIndex,n,Ipoly, nbVars); 
	Ipoly:= factor(Kw(Ipoly, nbVars)); 
	Ipoly:= z_to_m(Ipoly);
	return Ipoly;
end proc:

Iubar_n:= proc(n, poly_in_m)
	local sector, mbarbar, mbar,mubar, nbVars, Ipoly, theIndex;
	sector:= givePolySector(poly_in_m);
	mbarbar:= sector[4];
	mbar := sector[2];
	mubar:= sector[3];
	if mubar = 0 then return 0; end if;
        nbVars:= max(map(x-> nops(Flatten(x)), genN2spart(op(sector))));
	Ipoly:= old_LinBaseConvert(poly_in_m, 'z'); 
	Ipoly:= project_var_sector(Ipoly, "pt", sector); 
	Ipoly:= project_var_sector(Ipoly, "p", sector); 
	theIndex:= mbarbar+mbar+1;
	Ipoly:= theta||theIndex*diff(Ipoly, theta||theIndex);
	Ipoly:= Dunkl_i_n(theIndex,n,Ipoly, nbVars); 
	Ipoly:= factor(Kw(Ipoly, nbVars)); 
	Ipoly:= z_to_m(Ipoly);
	return Ipoly;
end proc:
testJn:= proc(n, poly_in_m)
	local poly_z, nbVars, Jpoly;
	poly_z:= old_LinBaseConvert(poly_in_m, 'z'); 
	nbVars:= giveNbVars(poly_z);
	Jpoly:= map(x-> theta||x*diff(poly_z, theta||x), [seq(k, k=1..nbVars)]); 
	Jpoly:= map(x-> factor(Dunkl_i_n(x, n, Jpoly[x])), [seq(k,k=1..nbVars)]); 
	Jpoly:= factor(add(k, k in Jpoly)); 
	return (Jpoly); 
end proc:

VAP_I:= proc(spart, i, N)
	local spart_sector, M_i, pts, phis, thetas, zeds, Rspart, ellComp, deltaNell, term1, term2, term3, j,m,thesign;
	spart_sector:= giveSpartSector(spart);
	spart_sector:= [spart_sector[4], spart_sector[2], spart_sector[3]];
	M_i:= [0,spart_sector[1],spart_sector[1] + spart_sector[2],spart_sector[1] + spart_sector[2]+ spart_sector[3]];
	pts:= spart[1];
	phis:= spart[2];
	thetas:= spart[3];
	zeds:= spart[4]; 
	Rspart:= [op(Reverse(pts)),op(Reverse(phis)), op(Reverse(thetas)), op(Reverse(zeds))];
	ellComp:= nops(Rspart);
	deltaNell:= N-ellComp;
	if deltaNell<>0 then Rspart:= [op(Rspart), seq(0, k=1..deltaNell)]; end if;
	print(Rspart, "rspart");
	ellComp:= N;
	term1:= factorial(N- (spart_sector[1] + spart_sector[2] + spart_sector[3]));
	print(term1, "globalpref"); 
	term2:= factorial( spart_sector[1]) * factorial(spart_sector[2]) * factorial(spart_sector[3]);
	term2:= term2/factorial(spart_sector[i]);
	print(term2, "specificpref"); 
	term3:= 
		add( factorial(M_i[i+1]-j)*( (M_i[i+1]-j)*lambdabar_i(Rspart,j, ellComp) - beta), j=(M_i[i]+1)..(M_i[i+1]-1)) 
		+ lambdabar_i(Rspart, M_i[i+1], ellComp);
	for j from M_i[i]+1 to M_i[i+1] - 1 do
		print("itt",j,"pref", factorial(M_i[i+1]-j));
		print("lambdabar", lambdabar_i(Rspart, j, ellComp)); 
		print("addedterm",factorial(M_i[i+1]-j)*( (M_i[i+1]-j)*lambdabar_i(Rspart,j, ellComp) - beta)) ;
		print((M_i[i+1]-j), hey);
	end do;
	print(M_i);
	print(lambdabar_i(Rspart, M_i[i+1], ellComp)); 
	return term1*term2*term3;
end proc:



EigenCMSn:= proc(spart,n, hn:=0, IorNot:=NULL, minN:=NULL)
    local DomMonomial, OpDomMonomial, I_1_1EigVal, I_2_1EigVal, H_2EigVal, EigenValues;
    # The function that returns the Eigen value for a given monomial. The code is probably broken.
    if minN <> NULL then DomMonomial:= m2n(spart, minN); else DomMonomial:= m2n(spart)  end if;

    I_1_1EigVal:=0;
    I_2_1EigVal:=0: 
    H_2EigVal:= 0;

    OpDomMonomial:= I_k_n(1,n, DomMonomial, 2);
    if OpDomMonomial <> 0 then 
        I_1_1EigVal:=  coeff(OpDomMonomial, m[op(spart)]);
    end if;

    OpDomMonomial:= I_k_n(6,n, DomMonomial, 2);
    if OpDomMonomial <> 0 then 
        I_2_1EigVal:= coeff(OpDomMonomial, m[op(spart)]);   
    end if;

    OpDomMonomial:= H_n(n+hn, DomMonomial);
    if OpDomMonomial <> 0 then 
        H_2EigVal:= coeff(OpDomMonomial, m[op(spart)]);
    end if;
    if IorNot=NULL then
        EigenValues:= [I_1_1EigVal, I_2_1EigVal, H_2EigVal]; 
    else
        #EigenValues:= [I_1_1EigVal+I_2_1EigVal,I_1_1EigVal-I_2_1EigVal, H_2EigVal]; 
        EigenValues:= [I_1_1EigVal,I_2_1EigVal, H_2EigVal]; 
    end if;
    return EigenValues;
end proc:
