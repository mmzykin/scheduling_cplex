/*********************************************
 * OPL 12.10.0.0 Model
 * Authors: Alexander De Munster, Bram D'haenens
 *********************************************/
using CP;
int nbTeams = ...;
range teams = 1..nbTeams;
int B = ...;
range byes = 0..B;
int nbRounds = 2*(nbTeams-1)+B;
range rounds = 1..nbRounds;
int Ub = ...;
int D[teams,teams]=...;
dvar int x[teams][teams] in 0..nbRounds;
dvar int v[1..nbTeams][0..nbRounds+1] in 1..nbTeams;
execute{
	writeln("Defining search strategy and setting parameters");
	cp.param.TimeLimit = 30*60;
	var f=cp.factory;
	var phase1 = f.searchPhase(x, f.selectSmallest(f.domainSize()),
									f.selectLargest(f.value()));
	var phase2 = f.searchPhase(v, f.selectSmallest(f.domainSize()),
									f.selectLargest(f.value()));
	cp.setSearchPhases(phase1, phase2);
	cp.param.PresolveLevel=6;
	cp.param.Workers = 4;
	cp.param.AllDiffInferenceLevel = 6;
	cp.param.CountInferenceLevel = 6;
}

minimize sum(i in teams,r in 0..nbRounds)D[v[i][r], v[i][r+1]];
subject to
{
	//One game per day
	forall(i in teams)
		allDifferent(append(all (j in teams: j!=i) x[i][j], all (j in teams) x[j][i]));
	//Not against self
	forall(i in teams)
		x[i][i] == 0;
	//Set venues
	forall(i,j in teams, r in rounds)
		x[i][j] == r => v[i][r] == i && v[j][r] == i;
	//Start and finish at home
	forall(i in teams){
		v[i][0] == i;
		v[i][nbRounds+1] == i;
	}
	//Stay at the same venue during a bye
	forall(i in teams, r in rounds)
		count(append(all(j in teams)x[i][j], all(j in teams)x[j][i]), r) == 0
													=> v[i][r] == v[i][r-1];
	// No repeat constraints
	forall(i,j in teams: i<j)
		abs(x[i][j] - x[j][i]) > 1;
	//At most constraints home games
	forall (b in byes,r in 1..nbRounds-Ub+b, i in teams)
		sum(n in 0..Ub+b)count(all(j in teams)x[i][j], r+n)== 0
				=> sum(n in 0..Ub+b)count(all(j in teams)x[j][i], r+n) <= Ub;
	//At most constraints away games
	forall (b in byes,r in 1..nbRounds-Ub+b, i,j in teams)
		sum(n in 0..Ub+b)count(all(j in teams)x[i][j], r+n)== 0
				=> sum(n in 0..Ub+b)count(all(j in teams)x[j][i], r+n) <= Ub;
	//Redundant Constraints
	forall (r in 1..nbRounds-Ub-B, i in teams) {
		sum(p in 0..Ub+B) count(all(j in teams) x[i][j], r+p) >= 1;
		sum(p in 0..Ub+B) count(all(j in teams) x[j][i], r+p) >= 1;
	}
	forall(i in teams, k in 1..nbTeams-1){
		sum(r in 1..nbRounds-k*(Ub+1)) count(all(j in teams) x[i][j], r) >= nbTeams-1-k*Ub;
		sum(r in 1..nbRounds-k*(Ub+1)) count(all(j in teams) x[j][i], r) >= nbTeams-1-k*Ub;
	}
	forall(r in rounds){
		count(all(i,j in teams: i!=j) x[i][j], r) <= nbTeams/2;
	}
	//Symmetry breaking
	x[1][2]>x[2][1];
	
	// maximum days in away series
	
	
	
	// minimum days in away series 
	
	
	// minimum days between series
	
	
	// at least 1 day of rest between games of one team 
	
	
	
}
