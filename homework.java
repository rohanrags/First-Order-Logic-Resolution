package ai4;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.management.ClassLoadingMXBean;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Scanner;
import java.util.Set;

import javax.swing.text.html.HTMLDocument.HTMLReader.IsindexAction;

public class homework {
	public static void main(String[] args) throws FileNotFoundException {
		Scanner sc = null;
		ArrayList<String> queries = new ArrayList<String>();
		ArrayList<String> statements = new ArrayList<String>();
		int nqueries,nStatements;

		sc = new Scanner(new File("./src/ai3/input.txt"));
		/*sc = new Scanner(new File("input.txt"));*/

		nqueries = sc.nextInt();
		sc.nextLine();
		for(int i=0;i<nqueries;i++) {
			StringBuilder br = new StringBuilder(sc.nextLine());
			for (int j = 0 ; j < br.length(); j++){
				if (br.charAt(j) == ' ' || br.charAt(j) == '\t' || br.charAt(j) == '\n'){
					br.replace(j, j+1, "");
					j--;
				}
			}
			queries.add(br.toString()); 
		}

		nStatements = sc.nextInt();
		sc.nextLine();
		for(int i=0;i<nStatements;i++) {
			StringBuilder br = new StringBuilder(sc.nextLine());
			for (int j = 0 ; j < br.length(); j++){
				if (br.charAt(j) == ' ' || br.charAt(j) == '\t' || br.charAt(j) == '\n'){
					br.replace(j, j+1, "");
					j--;
				}
			}
			statements.add(br.toString());
		}

		HashMap<String, List<String>> kb_map;
		List<String> classMap;

		classMap=create_classMap(statements); //creating classMap, basically has all statements of Kb in standardized form.
		kb_map=create_kbMap(classMap);

		ArrayList<Boolean> result = new ArrayList<>();
		for (String query : queries) {
			result.add(resolve(query, kb_map,classMap));
		}


		sc.close();

		//Output Result
		File outFile = new File("./src/ai3/output.txt");
		/*File outFile = new File("output.txt");*/
		try {
			FileWriter fileWriter = new FileWriter(outFile);

			for (Boolean b : result){
				if (b){
					fileWriter.write("TRUE\n");
					System.out.println("TRUE");
				} else {
					fileWriter.write("FALSE\n");
					System.out.println("FALSE");
				}
			}
			fileWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private static boolean resolve(String query, HashMap<String, List<String>> kb_map, List<String> classMap) {

		HashMap<String, List<String>> kb_map_copy;
		List<String> classMap_copy;

		//create copies of ClassMap and Kb_Map
		kb_map_copy = createCopyofKb_Map(kb_map);
		classMap_copy = createCopyofClass_Map(classMap);

		//add negated statement to classMap at zeroth position
		classMap_copy.add(0, negateStatement(query));

		int difference=-1;
		while(difference!=0) {
			int size = classMap_copy.size();
			for (int i=0;i<classMap_copy.size();i++) {
				if (classMap_copy.size() > 10000){
					return false;
				}
				if(unify(classMap_copy.get(i),classMap_copy,kb_map_copy))
					return true;
			}
			difference = classMap_copy.size()-size;
		}

		return false;
	}

	private static boolean unify(String query, List<String> classMap_copy, HashMap<String, List<String>> kb_map_copy) {

		String[] aTokens = query.split("\\|"); //Female(Alice)

		if(aTokens.length==1){
			String check = negateStatement(aTokens[0]);
			if (classMap_copy.contains(check)){
				return true;
			}
		}

		for(int i=0;i<aTokens.length;i++) {
			String aQuery = negateStatement(aTokens[i]); // aQuery = Female(Alice)
			String[] aArguments = getArguments(aQuery); // Get Arguments of aQuery - Alice
			String aPredicate = getPredicate(aQuery); //Get Predicate of aQuery - Female

			List<String> sentences = kb_map_copy.get(aPredicate); //Sentences that contain the aPredicate - Female in Kb_map


			boolean queryBelongs = false;
			if (sentences != null){
				for ( int j = 0; j < sentences.size(); j++){
					if(query.equals(sentences.get(j))){
						queryBelongs = true;
					}
				}
			}
			if (queryBelongs){
				continue;
			}

			if(sentences==null) 
				continue;
			for (int z=0;z<sentences.size();z++) {
				String bclause = sentences.get(z);
				String[] bTokens = bclause.split("\\|"); //bTokens = Female(x0),Human(x0)
				String bQuery = null;
				boolean can_unify=false;
				HashMap<String,String> argsMap = new HashMap<>(); //Arguments map to hold unified arguments. - If statements can be unified
				
				for(int j=0;j<bTokens.length;j++) {
					bQuery = bTokens[j]; // bQuery = Female(x0)
					String[] bArguments = getArguments(bQuery); // Get Arguments of bQuery - x0
					String bPredicate = getPredicate(bQuery); //Get Predicate of bQuery - Female
					
					if(aPredicate.equals(bPredicate)) { //Female==Female
						if(aArguments.length==bArguments.length) { //Length of aArguments==bArguments Alice and x0
							for(int k=0;k<aArguments.length;k++) {
								if(aArguments[k].equals(bArguments[k])) {
										//if both are constants/var and are equal - can be unified
										can_unify=true;
										argsMap.put(aArguments[k], aArguments[k]);
								} else {
									if(isAConstant(aArguments[k]) && isAConstant(bArguments[k])) {
										//both are different constants
										can_unify=false;
										break;
									} else if (isAConstant(aArguments[k])) {
										//A is constant
										can_unify=true;
										argsMap.put(bArguments[k], aArguments[k]);
									} else if (isAConstant(bArguments[k])) {
										//B is constant
										can_unify=true;
										argsMap.put(aArguments[k], bArguments[k]);
									} else {
										//A and B are variables.
										can_unify=true;
										argsMap.put(aArguments[k], bArguments[k]);
									}
								}
							}
							
							if(can_unify)
								break; //It means that the arguments can be unified. So can_unify will be true and we break.
						}
					}
				}

				if(can_unify) {
					// If this is true then it means that the aQuery and bQuery can be unified successfully.
					String newStringA = unify_statement(negateStatement(aQuery),query.split("\\|"),argsMap);
					String newStringB = unify_statement(bQuery,bclause.split("\\|"),argsMap);
					String resString = compare(newStringA,newStringB);

					if(resString.isEmpty() || resString.equals(""))
						return true;
					else {
						//Check if the resString is already present in the ClassMap
						if(classMap_copy.contains(resString))
							continue;
						
						classMap_copy.add(resString); //Else add it to the ClassMap

						String[] tokens = resString.split("\\|");
						if (tokens.length == 1){
							if (classMap_copy.contains(negateStatement(resString))){
								return true;
							}
						}

						add_to_Kb(resString,kb_map_copy); //Add to KB
					}
				}
			}
		}

		return false;
	}


	//Compares two unified strings and make them one resString
	private static String compare(String newStringA, String newStringB) {
		String resString="";
		if (newStringA.isEmpty() && newStringB.isEmpty()){
			return resString;
		} else if (newStringA.isEmpty()){
			resString = newStringB;
		} else if (newStringB.isEmpty()){
			resString = newStringA;
		} else {
			resString = newStringA+"|"+newStringB;
		}
		return resString;
	}

	//Unifies statement Tokens with aPredicate according to value in argsMap
	private static String unify_statement(String aPredicate, String[] Tokens, HashMap<String, String> argsMap) {
		String newString="";
		for(int m=0;m<Tokens.length;m++) {
			String str = Tokens[m]; // StringA = Female(Alice), Wanted Human(something) to unify in Query with |
			String str_Predicate = getPredicate(str); //Get StringA of aQuery - Female, Wanted Human to Unify
			if(!str.equals(aPredicate)) {
				String[] str_args = getArguments(str); // Get StringA of aQuery - Alice
				newString+=str_Predicate+'(';
				for(int n=0;n<str_args.length;n++) {
					if(argsMap.get(str_args[n])!=null)
						newString+=argsMap.get(str_args[n]);
					else
						newString+=str_args[n];

					if(n<str_args.length-1)
						newString+=',';
				}
				newString+=")";
				if (m !=  Tokens.length-1){
					newString += "|";
				}
			}
		}
		
		if(!newString.isEmpty() && newString.charAt(newString.length()-1) == '|'){
			newString = newString.substring(0, newString.length()-1);
		}

		return newString;
	}

	private static HashMap<String, List<String>> create_kbMap(List<String> classMap) {

		HashMap<String, List<String>> kb_map = new HashMap<>();	

		for (String clause : classMap){
			String[] predicates = clause.split("\\|"); //split the statement

			for ( int i =0 ; i < predicates.length; i++){
				predicates[i] = getPredicate(predicates[i]); //get only the predicate - no arguments
			}

			for ( int j=0 ; j < predicates.length; j++){
				if (kb_map.get(predicates[j]) != null){
					kb_map.get(predicates[j]).add(clause); // add the predicate to map
				} else {
					List<String> tokens = new ArrayList<String>();
					tokens.add(clause);
					kb_map.put(predicates[j], tokens); // add the predicate to map by creating new arrayList
				}
			}
		}
		return kb_map;
	}

	private static void add_to_Kb(String statement, HashMap<String, List<String>> kb_map) {
		String[] predicates = statement.split("\\|"); //split the statement

		for ( int i =0 ; i < predicates.length; i++){
			predicates[i] = getPredicate(predicates[i]); //get only the predicate - no arguments
		}

		for ( int j=0 ; j < predicates.length; j++){
			if (kb_map.get(predicates[j]) != null){
				kb_map.get(predicates[j]).add(statement); // add the predicate to map
			} else {
				List<String> tokens = new ArrayList<String>();
				tokens.add(statement);
				kb_map.put(predicates[j], tokens); // add the predicate to map by creating new arrayList
			}
		}
	}

	private static List<String> create_classMap(ArrayList<String> statements) {

		List<String> classMap = new ArrayList<String>();
		int statementCount=0;

		for (String statement : statements) {
			String res = "";
			String[] predicates = statement.split("\\|");
			for(int i=0;i<predicates.length;i++) {
				String predicate = predicates[i];
				boolean negated=false;

				if(predicate.charAt(0)=='~') {
					//if negation is present, since below code doesn't take ~ into account.
					negated=true;
					predicate=predicate.substring(1);
				}

				if (predicate.charAt(0) >= 65 && predicate.charAt(0) <= 90) {
					int openBracket = -1;
					int closingBracket = 0;

					while (predicate.charAt(closingBracket)!= ')'){
						if (predicate.charAt(closingBracket) == '('){
							openBracket = closingBracket;
						}
						closingBracket++;
					}

					int j=openBracket+1;//start from openBracket till closed bracket - convert all args into standardized format.
					while(predicate.charAt(j)!= ')') {
						if (predicate.charAt(j) >= 65 && predicate.charAt(j) <= 90) {
							while(predicate.charAt(j)!=',') {
								if(predicate.charAt(j)== ')')
									break;
								j++;
							}
							j--;
						} else if (predicate.charAt(j) >= 97 && predicate.charAt(j) <= 122) {
							predicate = predicate.substring(0, j+1)+statementCount+predicate.substring(j+1);
						}
						j++;
					}

					if(negated) { //if predicated is negated
						predicate="~"+predicate;
					}

					//adding the whole newPredicate to res to put whole string into the map.
					if(res!="") {
						res += "|" + predicate;
					} else {
						res += predicate;
					}
				}
			}

			classMap.add(res);
			statementCount++;			
		}
		return classMap;
	}

	private static List<String> createCopyofClass_Map(List<String> classMap) {
		List<String> classMap_copy = new ArrayList<String>();
		for (String item: classMap){
			classMap_copy.add(item);
		}
		return classMap_copy;
	}

	private static HashMap<String, List<String>> createCopyofKb_Map(HashMap<String, List<String>> kb_map) {
		HashMap<String,List<String>> kbMap_copy = new HashMap<String,List<String>>();
		Set<String> key = kb_map.keySet();
		for ( String k : key){
			List<String> list = kb_map.get(k);
			List<String> list_copy =  new ArrayList<String>();
			for (String item : list){
				list_copy.add(item);
			}
			kbMap_copy.put(k, list_copy);
		}

		return kbMap_copy;
	}

	private static String getPredicate(String query){
		String[] split = query.split("\\(");
		return split[0];
	}

	private static String[] getArguments(String token) {
		token = token.split("\\(")[1].split("\\)")[0];
		return token.split(",");
	}

	private static String negateStatement(String statement){
		if (statement.charAt(0) == '('){
			statement = statement.substring(1, statement.length()-1);
		}
		statement = "~"+statement;
		if (statement.substring(0, 2).equals("~~")){
			statement = statement.substring(2);
		}
		return statement;
	}

	private static boolean isAConstant(String string) {
		if (string.charAt(0) >= 65 && string.charAt(0) <= 90){
			return true;
		}
		return false;
	}
}
