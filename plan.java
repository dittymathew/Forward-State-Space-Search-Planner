package fssp;

import java.io.File;
import java.io.FileNotFoundException;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Properties;
import java.util.Set;

import org.paukov.combinatorics.Factory;
import org.paukov.combinatorics.Generator;
import org.paukov.combinatorics.ICombinatoricsVector;

import pddl4j.*;
import pddl4j.ErrorManager.Message;
import pddl4j.PDDLObject.Content;
import pddl4j.exp.AndExp;
import pddl4j.exp.AtomicFormula;
import pddl4j.exp.DerivedPredicate;
import pddl4j.exp.Exp;
import pddl4j.exp.InitEl;
import pddl4j.exp.NotAtomicFormula;
import pddl4j.exp.action.Action;
import pddl4j.exp.action.ActionDef;
import pddl4j.exp.term.Constant;
import pddl4j.exp.term.Substitution;
import pddl4j.exp.term.Term;
import pddl4j.exp.term.Variable;

public class plan {
 
    static ArrayList fsss_state =new ArrayList();
	public static void main(String[] args) throws FileNotFoundException {
	 
	    	 Properties options = new Properties();
	    	 options.put(RequireKey.STRIPS, true);
	    	 options.put(RequireKey.TYPING, true);
	    	 options.put(RequireKey.EQUALITY, true);
	    	 options.put(RequireKey.UNIVERSAL_PRECONDITIONS, true);
	    	 options.put(RequireKey.CONDITIONAL_EFFECTS, true);
	    	 options.put(RequireKey.NEGATIVE_PRECONDITIONS, true);
	    
	         // Creates an instance of the java pddl parser
	         Parser parser = new Parser(options);
	         Domain domain = parser.parse(new File("/home/aidb/workspace/fssp/src/fssp/blocksworld.pddl"));
	         Problem problem = parser.parse(new File("/home/aidb/workspace/fssp/src/fssp/pb4.pddl"));
	         PDDLObject obj = parser.link(domain, problem);
	         DerivedPredicate dp ;
	         
	         // Gets the error manager of the pddl parser
	         ErrorManager mgr = parser.getErrorManager();
	         
	         // If the parser produces errors we print it and stop
	         if (mgr.contains(Message.ERROR)) {
	             mgr.print(Message.ALL);
	         } // else we print the warnings
	         else {
	             mgr.print(Message.WARNING);
	             System.out.println("\nParsing domain \"" + domain.getDomainName()
	                         + "\" done successfully ...");
	             System.out.println("Parsing problem \"" + problem.getProblemName()
	                         + "\" done successfully ...\n");
	         }
	         //Initial state
	         List<InitEl> list =obj.getInit(); ///get initial state
	         System.out.println("Initial State");
	         System.out.println(list);
	         ArrayList curstate = new ArrayList();
	         curstate.addAll(list); ///store the initial state to curstate
	         ArrayList actions = new ArrayList(); 
	         ArrayList goal = new ArrayList();
	         Exp ex =obj.getGoal(); ///get goal state
	   	   	 AndExp andExp = (AndExp) ex; ///goal state is type cast to AndExp
	   	   	 Iterator<Exp> j = andExp.iterator(); //Iterating over predicates
	       	 while(j.hasNext()){
	       		Object oj =j.next();
	       		goal.add(oj); ///adding goal predicates to arraylist goal
	       	 }
	       	 fsss_state.add(curstate); ///adding initial state to global state list fsss_state
	       	 
	       	ArrayList<AtomicFormula> newplan = new ArrayList<AtomicFormula>();
	       	System.out.println("Goal State");
	         System.out.println(goal);
	         plan.forward_search(curstate,obj,goal,null,0);///Calling fowrad state space plan
	         
	        
	     }
	/*
	 * Function: forward_search()
	 * Arguments: state- holds current state
	 * 			  obj - Pddl object
	 * 			  goal - Goal state
	 * 			  newplan - Current plan
	 * 
	 * Purpose : Recursive implementation of Forward state space search
	 * 
	 * 
	 */
	public static int forward_search(ArrayList state,PDDLObject obj, ArrayList goal, ArrayList<AtomicFormula> newplan,int level)
	{
		int p = 0;
		int i;
		ArrayList act_grounded =new ArrayList();
		ArrayList effect =new ArrayList();
		ArrayList newstate = new ArrayList();
		
		//Goal Test
		if(state.containsAll(goal)){
			System.out.println("myplan");
			for(i=newplan.size()-1;i>=0;i--)
				System.out.println(newplan.get(i)); //Printing plan
			return 1;
		}
		Applicable ap;
		ap=plan.findApplicable(state,obj,level);///find applicable actions
		act_grounded = ap.getActions(); //get applicable actions
		effect=ap.getEffect(); //get effects of applicable actions
	    if(act_grounded.size()==0){ ///check if there is no applicable actions
        	return 0;
        }
        i=0;
        Iterator itr = act_grounded.iterator();
        Iterator itrE = effect.iterator();
        
       //To process applicable actions
       for(i=0; i<act_grounded.size(); ++i){ ///for each applicable actions
        	newstate =getNextState(state,level,effect.get(i));
        	// Check whether newstate is visited or not
        	if(checkRevisit(newstate)){ //if not visited
        		//Collections.sort(newstate);
        		fsss_state.add(newstate); //adding to state list
        		//System.out.println(newstate);
        	//	System.out.println(act_grounded.get(i));
        		ArrayList<AtomicFormula> fsss_plan = new ArrayList<AtomicFormula>();
        		fsss_plan.add((AtomicFormula) act_grounded.get(i)); //adding to plan list
        		if(newplan != null)
        			fsss_plan.addAll(newplan); //appening to existing plan
        		
        		p=plan.forward_search(newstate,obj,goal,fsss_plan,++level ); ///recursive call for fssp
        		
        		
        	}
        	
        	
        }
        
        return 0;
	}
	/*
	 * Function to get next state give a state and and actions effects
	 */
	public static ArrayList getNextState(ArrayList state,int level,Object effect){
		ArrayList newstate =new ArrayList();
		
		//effect= ap.getEffect();
		AndExp andExp = (AndExp) effect; ///get corres[ponding effects
    	ArrayList poseff = new ArrayList();
		ArrayList negeff = new ArrayList();
   	   	 Iterator<Exp> j = andExp.iterator();
       	 while(j.hasNext()){ ///for each predicates in the effect
       		 Object oj =j.next();
       		 if(oj.getClass().equals(AtomicFormula.class)) ///check for positive effects
       			poseff.add(oj); ///add to positive effect list
       		 else if(oj.getClass().equals(NotAtomicFormula.class)) ///check for negative effects
       		{
       			 NotAtomicFormula naf = (NotAtomicFormula)oj;
       			 negeff.add(naf.getExp()); /// add to negative effect list
       		
       		}
       	 }
       	 for(int k=0;k<state.size();k++){
       		newstate.add(state.get(k)); ///copying current state to newstate
       	 }
       	for(int k=0;k<negeff.size();k++){ ///removing negative effects from newstate
       		for(int ki=0;ki<state.size();ki++){
       			if(state.get(ki).equals(negeff.get(k))){
       				
       				newstate.remove(state.get(ki));
       				break;
       			}
       				
       		}
       	 }

       	for(int kj=0;kj<poseff.size();kj++){ ///Adding positive effects to newstate
       		int k3=0;
       		for(int ki=0;ki<state.size();ki++){
       			if(state.get(ki).equals(poseff.get(kj))){
       				k3=1;
       				break;
       			}
       		}
       		if(k3==0)
       			newstate.add(poseff.get(kj));
   			
   		}
       	return newstate;
	}

	public static boolean checkEquals(ArrayList state, ArrayList newstate){
		boolean k= false;
		int i,j,count;
		count =0;
		if(state.size()!=newstate.size())
			return k;
		for(i=0;i<state.size();i++){
			for(j=0;j<newstate.size();j++){
				if(state.get(i).equals(newstate.get(j))){
					count++;
					break;
				}
			}
		}
		if(count==state.size() && count==newstate.size()){
			///System.out.println("State :"+state);
			//System.out.println("NewState"+ newstate);
			return true;
		}
		return k;
	}
	/*
	 * Function to check revisiting
	 * Returns true if not visited
	 * 		   false if visited
	 */
	public static boolean checkRevisit(ArrayList state){
		boolean k =true;
		//System.out.println("in cherevist"+ state+" \n old"+fsss_state);
		if(fsss_state.isEmpty())
			return k;
		int k6;
       	for(k6=0;k6<fsss_state.size();k6++){
       		if(checkEquals(state,(ArrayList) fsss_state.get(k6))){
       			k=false;
       			
       		}
        }
       	
       		
       	return k;
	}
	

	/*
	 * Find applicable actions
	 */
	public static Applicable findApplicable(ArrayList curstate, PDDLObject obj,int level){
		 //	ArrayList  act_grounded =new ArrayList();
		 	ArrayList effect =new ArrayList();
			ArrayList pre_apply = new ArrayList();
	        ArrayList app_actions = new ArrayList();
	        ArrayList constants = new ArrayList();
	       // act_grounded[level].removeAll(act_grounded[level]);
	       // effect_grounded[level].removeAll(effect_grounded[level]);
	        Iterator<Constant> ic = obj.constantsIterator();
			while(ic.hasNext()) { ///storing constants to a list
				Object ob= ic.next();
				constants.add(ob);
			}
	        Iterator <ActionDef> act = obj.actionsIterator();
	        while(act.hasNext()) ///Iterating for each actions
	        {
	        	
	        	ActionDef actionDef =act.next();
	   	   		Action action = (Action)actionDef;
	   	   	
	            Exp exp = action.getPrecondition(); //get preconditions
	            AndExp andExp = (AndExp) exp;
	            Set<Variable> fv = action.getPrecondition().getFreeVariables(); ///get free variables in preconditions
				int nfv = fv.size();	/// storing free variable size	
				
				if(nfv==1){
					
					Iterator itr2 = fv.iterator();
					while(itr2.hasNext()) { ///iterating over free variable
						
						Variable var = (Variable) itr2.next();
						
						Iterator<Constant> itr3 = obj.constantsIterator(); 
						while(itr3.hasNext()) { ///Iterating over constants
							Constant cons = itr3.next();
							Substitution sigma = new Substitution();
							sigma.bind(var, cons); ///binding constant to variable

							
							Iterator<Exp> itr1 = andExp.iterator();
							while(itr1.hasNext()) {

								Exp pc = itr1.next();		
								pc = pc.apply(sigma); ///substituting variables in preconditions
								AtomicFormula af = (AtomicFormula) pc;
								pre_apply.add(pc); ///store the substituted precondition 
							}
							
							if(curstate.containsAll(pre_apply)){
							{
								
								Exp exp_eff =action.getEffect(); ///get effects of action
		        					exp_eff.apply(sigma); ///substituting to effects
		        					AtomicFormula name = new AtomicFormula(action.getName());
		        					for (Term p : action.getParameters()) {
		        						Term p_cnst =(Term)sigma.getBinding((Variable) p);// binding variables to action
		        						if(p_cnst != null)
		        						name.add(p_cnst);
		        						//name.add((Term)sigma.getBinding((Variable) p));
		        		           
		        					}
		        					app_actions.add(name); //store grounded action
		        					effect.add(exp_eff.apply(sigma));///store grounded effects
		        					
							}
							
						}
							pre_apply.removeAll(pre_apply);
					}
					}
				}else{
					ArrayList<ArrayList<Constant>> constCombi = genComb(constants,nfv);	
					//System.out.println(constCombi);
					Iterator<ArrayList<Constant>> itrConst = constCombi.iterator();
					while(itrConst.hasNext()) {
						
						ArrayList<Constant> cons = itrConst.next();					
						Substitution sigma = new Substitution();					

						Iterator itr2 = fv.iterator();
						Iterator itr3 = cons.iterator();
						while(itr2.hasNext()&&itr3.hasNext()) {				

							Variable var = (Variable) itr2.next();
							Constant constant = (Constant) itr3.next();
							sigma.bind(var, constant);
						}

						Iterator<Exp> itr1 = andExp.iterator();
						while(itr1.hasNext()) {

							Exp pc = itr1.next();	
							pc = pc.apply(sigma);
							pre_apply.add((AtomicFormula) pc);
						}
						
						if(curstate.containsAll(pre_apply)){
						{
							
							Exp exp_eff =action.getEffect();
		        				exp_eff.apply(sigma);
		        				AtomicFormula name = new AtomicFormula(action.getName());
		        				for (Term p : action.getParameters()) {
		        					Term p_cnst =(Term)sigma.getBinding((Variable) p);
		        					if(p_cnst != null)
		        					name.add(p_cnst);
		        					//name.add((Term)sigma.getBinding((Variable) p));
		        		          
		        				}
		        				app_actions.add(name);
		        				effect.add(exp_eff.apply(sigma));
		        				
		        				
						}
						
					}
						pre_apply.removeAll(pre_apply);
				}
	        	
	        }
	        }
	    Applicable a=new Applicable();
	    a.setActions(app_actions);
	    a.setEffect(effect);
	    
		return a;
		}
	/*
	 * Credit to http://code.google.com/p/combinatoricslib/
	 * Credit to Ashika
	 */
		public static ArrayList<ArrayList<Constant>> genComb(ArrayList constants, int noFreeVar) {

			ArrayList<ArrayList<Constant>> comb = new ArrayList<ArrayList<Constant>>();
			String fv[] = new String[constants.size()];
			for(int i=0,j=0;j<constants.size();i++,j++) {
				fv[i]=constants.get(j).toString();
			}
			ICombinatoricsVector<String> initialVector = Factory.createVector(fv);
			Generator<String> gen = Factory.createSimpleCombinationGenerator(initialVector, noFreeVar);

			for (ICombinatoricsVector<String> combination : gen) {

				java.util.List<String> l = combination.getVector();

				ICombinatoricsVector<String> temp = Factory.createVector(l);
				Generator<String> genPerm = Factory.createPermutationGenerator(temp);

				for (ICombinatoricsVector<String> perm : genPerm) {

					java.util.List<String> p = perm.getVector();
					ArrayList<Constant> c = new ArrayList<Constant>();
					Iterator<String> itr = p.iterator();
					while(itr.hasNext()) {
						c.add(new Constant(itr.next()));				
					}

					comb.add(c);
				}
			}	

			return comb;
		}


}
class Applicable{
	 	ArrayList  act_grounded ;
	    ArrayList effect_grounded ;
	    public Applicable(){
	    	 act_grounded =new ArrayList();
	    	 effect_grounded =new ArrayList();
	    }
	    public ArrayList getActions(){
	    	return this.act_grounded;
	    }
	    public ArrayList getEffect(){
	    	return this.effect_grounded;
	    }
	    public void setActions(ArrayList act){
	    	this.act_grounded =act;
	    }
	    public void setEffect(ArrayList effect){
	    	this.effect_grounded =effect;
	    }
}
