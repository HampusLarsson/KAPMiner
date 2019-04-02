import com.carrotsearch.hppc.IntObjectMap;
import com.carrotsearch.hppc.IntObjectOpenHashMap;
import org.apache.commons.cli.*;
import org.apache.commons.math3.util.Precision;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;
//Jag har lagt till en kommentar
/**
 * Created by isak on 2017-04-21.
 */
public class KAPMiner {

    private static double minSup,minConf,minSupRatio;
    private static int orderConstraint;
    private static Map<ItemSet, Double> supports;
    private static Map<ItemSet, List<RuleWithTransactions>> currentLevelMap , prevLevelMap ;
    private static List<ItemsetWithTransactions> nextLevel;
    private static List<Rule> outputRules;




    private static class Rule {
        private final ItemSet x, y;
        private final double support, supportRatio, confidence, lift;

        public Rule(RuleWithTransactions rule) {
            this.x = rule.x;
            this.y = rule.y;
            this.support = rule.support;
            this.supportRatio = rule.supportRatio;
            this.confidence = rule.getORconf();
            this.lift = rule.getLift();
        }

        public ItemSet getX() {
            return x;
        }

        public ItemSet getY() {
            return y;
        }

        public double getSupport() {
            return support;
        }

        public double getSupportRatio() {
            return supportRatio;
        }

        public double getConfidence() {
            return confidence;
        }

        public double getLift() {
            return lift;
        }
    }

    private static class RuleWithTransactions {

        private final BitSet transactions;
        private final ItemSet x, y;

        private final double support, supportRatio, ORconf;
        private final double lift;

        public RuleWithTransactions(ItemSet x, ItemSet y, BitSet transactions, double ruleSup,
                                    double supportRatio, double confidence, double lift) {
            this.x = x;
            this.y = y;
            this.transactions = transactions;
            this.ORconf = confidence;
            this.support = ruleSup;
            this.supportRatio = supportRatio;
            this.lift = lift;
        }

        public double getSupport() {
            return support;
        }

        public double getSupportRatio() {
            return supportRatio;
        }

        public double getORconf() {
            return ORconf;
        }

        public double getLift() {
            return lift;
        }

        public double frequency() {
            return transactions.cardinality();
        }

        @Override
        public String toString() {
            return "{<" + x + " => " + y + "> freq: " + transactions + "}";
        }
    }

    private static class ItemPosition {
        private final Map<Integer, Position> itemPosition;

        public ItemPosition() {
            this.itemPosition = new HashMap<>();
        }

        public void putAndExpand(int item, Position position) {
            Position pos = itemPosition.get(item);
            if (pos == null) {
                itemPosition.put(item, position);
            } else {
                pos.expand(position);
            }
        }

        public Position get(int item) {
            return itemPosition.get(item);
        }

        @Override
        public String toString() {
            return "ItemPosition{" + "itemPosition=" + itemPosition + '}';
        }
    }

    private static class Position {
        private int first, last;

        public Position(int first, int last) {
            this.first = first;
            this.last = last;
        }

        public int getFirst() {
            return first;
        }

        public int getLast() {
            return last;
        }

        public void expand(Position other) {
            this.first = Math.min(this.first, other.first);
            this.last = Math.max(this.last, other.last);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o)
                return true;
            if (o == null || getClass() != o.getClass())
                return false;

            Position that = (Position) o;
            if (first != that.first)
                return false;
            return last == that.last;
        }

        @Override
        public int hashCode() {
            int result = first;
            result = 31 * result + last;
            return result;
        }

        @Override
        public String toString() {
            return "{" + "first=" + first + ", last=" + last + '}';
        }
    }

    private static class ItemSet {

        private final int[] items;
        private double support;

        private ItemSet(int[] items) {
            this.items = items;
        }

        public int get(int i) {
            return items[i];
        }

        public int size() {
            return items.length;
        }

        public boolean prefixMatch(ItemSet other, int prefixSize) {
            // assume sorted and both have size < prefixSize
            for (int i = 0; i < prefixSize; i++) {
                if (items[i] != other.items[i]) {
                    return false;
                }
            }
            return true;
        }

        public boolean contains(ItemSet other) {
            int i = 0, j = 0;
            while (i < other.items.length && j < this.items.length) {
                if (this.items[j] < other.items[i]) {
                    j++;
                } else if (this.items[j] == other.items[i]) {
                    j++;
                    i++;
                } else if (this.items[j] > other.items[i]) {
                    return false;
                }
            }
            return i >= other.items.length;
        }

        public synchronized ItemSet merge(ItemSet b, int prefixSize) {
            int[] union = new int[this.items.length + 1];
            System.arraycopy(this.items, 0, union, 0, prefixSize);
            if (this.items[prefixSize] < b.items[prefixSize]) {
                union[prefixSize] = this.items[prefixSize];
                union[prefixSize + 1] = b.items[prefixSize];
            } else {
                union[prefixSize] = b.items[prefixSize];
                union[prefixSize + 1] = this.items[prefixSize];
            }
            return new ItemSet(union);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o)
                return true;
            if (o == null || getClass() != o.getClass())
                return false;

            ItemSet other = (ItemSet) o;
            return Arrays.equals(items, other.items);
        }

        @Override
        public int hashCode() {
            return Arrays.hashCode(items);
        }

        @Override
        public String toString() {
            return "{" + Arrays.stream(items).mapToObj(Integer::toString).collect(Collectors.joining(","))
                    + "}";
        }
    }

    private static class ItemsetWithTransactions {
        private ItemSet itemSet;
        private final BitSet transactions;

        public ItemsetWithTransactions(ItemSet item, BitSet transactions) {
            this.itemSet = item;
            this.transactions = transactions;
        }

        public double frequency() {
            return transactions.cardinality();
        }

        public BitSet getTransactions() {
            return transactions;
        }

        public ItemSet getItemSet() {
            return itemSet;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o)
                return true;
            if (o == null || getClass() != o.getClass())
                return false;

            ItemsetWithTransactions itemSet = (ItemsetWithTransactions) o;
            return this.itemSet.equals(itemSet.itemSet);
        }

        @Override
        public int hashCode() {
            return itemSet.hashCode();
        }

        @Override
        public String toString() {
            return "#{" + itemSet + " freq:" + frequency() + "}";
        }
    }

    public static synchronized BitSet intersection(BitSet a, BitSet b) {
        BitSet clone;
        BitSet and;
        if (a.size() < b.size()) {
            clone = a;
            and = b;
        } else {
            clone = b;
            and = a;
        }

        BitSet intersection = (BitSet) clone.clone();
        intersection.and(and);
        return intersection;
    }

    public static void main(String[] args) throws IOException {

        Options options = new Options();
        options.addOption("minSup", true, "minimum support");
        options.addOption("minSupRatio", true, "minimum support ratio");
        options.addOption("minConf", true, "minimum confidence");
        options.addOption("delta", true, "min temporal distance");
        options.addOption("input", true, "input file (use -time if time information is given)");
        options.addOption("time", false, "true if file contains no temporal information (event label, time)");
        options.addOption("output", true, "file for writing the results (default: write to standard out)");

        CommandLineParser parser = new DefaultParser();
        CommandLine cmd;
        try {
            cmd = parser.parse(options, args);


            String file = cmd.getOptionValue("input");
            if (file == null) {
                throw new RuntimeException("no input");
            }
            TransactionInput transactionInput = readTransactions(file, !cmd.hasOption("time"));

            minSup = Double.parseDouble(cmd.getOptionValue("minSup", "0.1"));
            minSupRatio = Double.parseDouble(cmd.getOptionValue("minSupRatio", "0.0"));
            minConf = Double.parseDouble(cmd.getOptionValue("minConf", "0.4"));;
            orderConstraint = Integer.parseInt(cmd.getOptionValue("delta", "1"));

            long start = System.currentTimeMillis();

            //Start extraction
            List<Rule> rules = findFrequent(transactionInput);

            String output = cmd.getOptionValue("output", "<std>");
            PrintStream out;
            if ("<std>".equalsIgnoreCase(output)) {
                out = System.out;
            } else {
                out = new PrintStream(new FileOutputStream(output));
            }
            System.err.printf("Found %d rules in %d ms with %.4f MB memory %n", rules.size(),
                    System.currentTimeMillis() - start,
                    (Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()) / 1024.0
                            / 1024.0);
            out.printf("Rule, support, supportRatio, conf, lift%n");
            rules.stream().sorted(Comparator.comparing(Rule::getSupport).reversed()).forEach(rule -> {
                out.printf("\"%s => %s\",%f,%f,%f,%f%n", rule.x, rule.y, rule.getSupport(),
                        rule.getSupportRatio(), rule.getConfidence(), rule.getLift());
            });

            out.flush();
        } catch (Exception e) {
            e.printStackTrace();
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp("KAPMinerTest", options);
            System.exit(0);
        }
    }

    private static List<Rule> findFrequent(TransactionInput transactionInput) {
        //Supports behöver skickas med
        supports = new HashMap<>();

        //intemPositionMap behövs skickas med
        IntObjectMap<ItemPosition> itemPositionMap = transactionInput.itemPositions;
        // noTransactions behöver skickas med
        double noTransactions = transactionInput.getTransactions();

        //currentLevel behöver skickas med
        List<ItemsetWithTransactions> currentLevel = new ArrayList<>();
        for (Map.Entry<Integer, BitSet> kv : transactionInput.getItemSets().entrySet()) {
            if (kv.getValue().cardinality() / noTransactions >= minSup) {
                ItemSet item = new ItemSet(new int[] {kv.getKey()});
                currentLevel.add(new ItemsetWithTransactions(item, kv.getValue()));
                supports.put(item, kv.getValue().cardinality() / noTransactions);
            }
        }

        //Behöver skickas med till tråd
        outputRules = new ArrayList<>();
        nextLevel = new ArrayList<>();

        currentLevelMap = new HashMap<>();
        prevLevelMap = new HashMap<>();
/**
 *
 *
 *
 *
 *
 *
 *
 *
 * Algoritm börjar här
 */
        int level = 1;
        boolean finished = false;
        while (true) {
            //For-loopen kan eventuellt parallelliseras
            ExecutorService es = Executors.newCachedThreadPool();

            //Rule extraction
            for (int i = 0; i < currentLevel.size(); i++) {

                es.execute(new RuleExtractor(currentLevel, itemPositionMap , noTransactions, i, level));


            }
            es.shutdown();
            do{
                try{
                    finished = es.awaitTermination(1000, TimeUnit.MILLISECONDS);
                }catch(InterruptedException ie){

                }
            }
            while(!finished);
            finished = false;



            if (!nextLevel.isEmpty()) {
                // levels.add(nextLevel);
                currentLevel.clear();
                List<ItemsetWithTransactions> tmp = currentLevel;
                currentLevel = nextLevel;
                nextLevel = tmp;

                prevLevelMap.clear();
                Map<ItemSet, List<RuleWithTransactions>> tmpMap = prevLevelMap;
                prevLevelMap = currentLevelMap;
                currentLevelMap = tmpMap;

                level += 1;
            } else {
                break;
            }
        }
        return outputRules;
    }

    private static BitSet itemIntersect(int orderConstraint,
                                        IntObjectMap<ItemPosition> itemPositionMap, BitSet intersectingTransactions, int itemA,
                                        int itemB) {
        BitSet beforeIntersection = new BitSet();
        for (int transactionId =
             intersectingTransactions.nextSetBit(0); transactionId >= 0; transactionId =
                     intersectingTransactions.nextSetBit(transactionId + 1)) {
            ItemPosition pos = itemPositionMap.get(transactionId);
            if (pos.get(itemB).getLast() - pos.get(itemA).getFirst() >= orderConstraint) {
                beforeIntersection.set(transactionId);
            }
            if (transactionId == Integer.MAX_VALUE) {
                break; // or (i+1) would overflow
            }
        }
        return beforeIntersection;
    }

    private static synchronized ItemSet mergeAntecedents(List<RuleWithTransactions> consequents, int size) {
        int[] union = new int[size + 1];
        Arrays.fill(union, Integer.MAX_VALUE);
        for (int i = 0; i < size; i++) {
            for (RuleWithTransactions rule : consequents) {
                int cons = rule.y.get(i);
                if (cons < union[i]) {
                    union[i] = cons;
                }
                union[i + 1] = cons;
            }

        }
        return new ItemSet(union);
    }

    private static synchronized ItemSet mergeConsequents(List<RuleWithTransactions> antecedents, int size) {
        int[] union = new int[size + 1];
        // Arrays.fill(union, Integer.MAX_VALUE);
        for (int i = 0; i < size; i++) {
            for (RuleWithTransactions rule : antecedents) {
                int cons = rule.x.get(i);
                if (cons < union[i] || union[i] == 0) {
                    union[i] = cons;
                }
                union[i + 1] = cons;
            }

        }
        return new ItemSet(union);
    }


    private static class TransactionInput {
        private final Map<Integer, BitSet> itemSets;
        private final double transactions;
        private final IntObjectMap<ItemPosition> itemPositions;


        private TransactionInput(Map<Integer, BitSet> itemSets, double transactions,
                                 IntObjectMap<ItemPosition> itemPositions) {
            this.itemSets = itemSets;
            this.transactions = transactions;
            this.itemPositions = itemPositions;
        }

        public double getTransactions() {
            return transactions;
        }

        public Map<Integer, BitSet> getItemSets() {
            return itemSets;
        }

        public ItemPosition getPosition(int transaction) {
            return itemPositions.get(transaction);
        }

    }

    private static List<List<Event>> readEventTransactions(String file) {
        Path path = Paths.get(file);
        try {
            List<List<Event>> transactions = new ArrayList<>();
            List<String> lines = Files.readAllLines(path);
            for (String line : lines) {
                List<Event> transaction = new ArrayList<>();
                String[] events = line.trim().split("\\s+");
                for (String event : events) {
                    String[] split = event.split(",");
                    transaction.add(new Event(Integer.parseInt(split[0]), Integer.parseInt(split[1])));
                }
                transactions.add(transaction);
            }
            return transactions;
        } catch (IOException e) {
            e.printStackTrace();
        }

        return null;
    }

    private static class Event {
        int value;
        int time;

        public Event(int value, int time) {
            this.value = value;
            this.time = time;
        }

        public int getValue() {
            return value;
        }

        public int getTime() {
            return time;
        }
    }

    private static TransactionInput readTransactions(String file, boolean b) {
        Map<Integer, BitSet> items = new HashMap<>();

        IntObjectMap<ItemPosition> itemPosition = new IntObjectOpenHashMap<>();
        List<List<Event>> transactions;
        if (b) {
            transactions = readSimpleEventTransactions(file);
        } else {
            transactions = readEventTransactions(file);
        }

        int transactionId = 0;
        for (List<Event> transaction : transactions) {
            ItemPosition pos = new ItemPosition();
            for (Event item : transaction) {
                if (items.containsKey(item.getValue())) {
                    items.get(item.getValue()).set(transactionId);
                } else {
                    BitSet trans = new BitSet();
                    trans.set(transactionId);
                    items.put(item.getValue(), trans);
                }
                pos.putAndExpand(item.getValue(), new Position(item.getTime(), item.getTime()));
            }
            itemPosition.put(transactionId, pos);
            transactionId++;
        }
        return new TransactionInput(items, transactions.size(), itemPosition);
    }

    private static List<List<Event>> readSimpleEventTransactions(String file) {

        Path path = Paths.get(file);
        try {
            List<List<Event>> transactions = new ArrayList<>();
            List<String> lines = Files.readAllLines(path);
            for (String line : lines) {
                List<Event> transaction = new ArrayList<>();
                String[] events = line.trim().split("\\s+");
                for (int i = 0; i < events.length; i++) {
                    String event = events[i];
                    transaction.add(new Event(Integer.parseInt(event), i));
                }
                transactions.add(transaction);
            }
            return transactions;
        } catch (IOException e) {
            e.printStackTrace();
        }

        return null;
    }


    private static synchronized void addSupport(ItemSet newItemSet, double support){
        supports.put(newItemSet,support);
    }
    private static synchronized void addRuleToCurrentLevelMap(ItemSet newItemSet, List<RuleWithTransactions> rules){
        currentLevelMap.put(newItemSet, rules);
    }
    private static synchronized void addRulePrevLevelMap(ItemSet newItemSet, List<RuleWithTransactions> rules){
        prevLevelMap.put(newItemSet, rules);
    }
    private static synchronized void addToNextLevel(ItemsetWithTransactions itemsetWithTransactions){

        nextLevel.add(itemsetWithTransactions);
    }
    private static synchronized void addToOutputRules(Rule rule){

        outputRules.add(rule);
    }

    //------------------------INNER-CLASS------------------------------
    private static class RuleExtractor implements Runnable{
        private List<ItemsetWithTransactions> currentLevel;
        private double noTransactions;
        private BitSet intersectingTransactions;
        private List<RuleWithTransactions> rules;
        private int i, level;
        private IntObjectMap<ItemPosition> itemPositionMap;
        //--------------------------------CONSTRUCTORS-----------------------------------
        //int i bör döpas om för tydlighetens skull
        public RuleExtractor(List<ItemsetWithTransactions> currentLevel, IntObjectMap<ItemPosition> itemPositionMap ,
                             double noTransactions, int i, int level){
            this.i = i;
            this.level = level;

            this.currentLevel = currentLevel;
            this.noTransactions = noTransactions;
            this.itemPositionMap = itemPositionMap;

        }
        //--------------------------------METHODS----------------------------------------
        @Override
        public void run(){
            for (int j = i + 1; j < currentLevel.size(); j++) {
                List<RuleWithTransactions> matches = new ArrayList<>();
                ItemsetWithTransactions iItem = currentLevel.get(i);
                ItemsetWithTransactions jItem = currentLevel.get(j);

                if (iItem.getItemSet().prefixMatch(jItem.getItemSet(), level - 1)) {
                    //intersection metoden kan behöva synkas
                    intersectingTransactions =
                            intersection(iItem.getTransactions(), jItem.getTransactions());
                    if (minSup >= intersectingTransactions.cardinality() / noTransactions)
                        continue;

                    //Merge behöver synkas
                    double itemsetSup = intersectingTransactions.cardinality() / noTransactions;
                    ItemSet newItemSet = iItem.getItemSet().merge(jItem.getItemSet(), level - 1);
                    addSupport(newItemSet, itemsetSup);

                    matches.clear();
                    List<RuleWithTransactions> iItemRules = prevLevelMap.get(iItem.getItemSet());
                    if (iItemRules != null) {
                        matches.addAll(iItemRules);
                    }
                    List<RuleWithTransactions> jItemRules = prevLevelMap.get(jItem.getItemSet());
                    if (jItemRules != null) {
                        matches.addAll(jItemRules);
                    }
                    rules = new ArrayList<>();
                    if (level > 1) {
                        extractRules(newItemSet, matches);
                    } else {
                        extractRulesOnFirstLevel(iItem, jItem);
                    }

                    addToNextLevel(new ItemsetWithTransactions(newItemSet, intersectingTransactions));
                    addRuleToCurrentLevelMap(newItemSet, rules);
                } else {
                    break;
                }
            }
        }
        private void extractRules(ItemSet newItemSet, List<RuleWithTransactions> matches){
            int[] tmpItemSet = new int[newItemSet.size() - 1];
            for (int k = newItemSet.size() - 3; k >= 0; k--) {
                int tmpCnt = 0;
                for (int l = 0; l < newItemSet.size(); l++) {
                    if (k != l) {
                        tmpItemSet[tmpCnt++] = newItemSet.get(l);
                    }
                }

                List<RuleWithTransactions> ruleWithTransactions = prevLevelMap.get(new ItemSet(tmpItemSet));
                if (ruleWithTransactions != null) {
                    matches.addAll(ruleWithTransactions);
                }
            }

            Set<ItemSet> usedX = new HashSet<>();
            Set<ItemSet> usedY = new HashSet<>();
            for (int k = 0; k < matches.size(); k++) {
                List<RuleWithTransactions> xs = new ArrayList<>();
                List<RuleWithTransactions> ys = new ArrayList<>();

                RuleWithTransactions r = matches.get(k);
                boolean checkedX = usedX.contains(r.x);
                boolean checkedY = usedY.contains(r.y);


                if (!checkedX) {
                    xs.add(r);
                    usedX.add(r.x);
                }

                if (!checkedY) {
                    ys.add(r);
                    usedY.add(r.y);
                }

                for (int l = k + 1; l < matches.size(); l++) {
                    RuleWithTransactions o = matches.get(l);
                    if (!checkedX && o.x.equals(r.x)) {
                        xs.add(o);
                    }
                    if (!checkedY && o.y.equals(r.y)) {
                        ys.add(o);
                    }
                }

                // If the number of itemsets to merge for the y
                if (xs.size() == level + 1 - r.x.size()) {
                    BitSet inter = new BitSet();
                    inter.or(xs.get(0).transactions);
                    for (int i1 = 1; i1 < xs.size(); i1++) {
                        RuleWithTransactions rule = xs.get(i1);
                        inter.and(rule.transactions);
                    }

                    double ruleSup = inter.cardinality() / noTransactions;
                    if (ruleSup >= minSup) {
                        double supportRatio =
                                inter.cardinality() / (double) intersectingTransactions.cardinality();
                        //mergeAntecedents behöver synkas
                        ItemSet mergedAntecedent = mergeAntecedents(xs, xs.size() - 1);
                        if (usedY.contains(mergedAntecedent)) {
                            continue;
                        }
                        double confidence = ruleSup / supports.get(r.x);
                        double lift = ruleSup / (supports.get(mergedAntecedent) * supports.get(r.x));
                        RuleWithTransactions rule = new RuleWithTransactions(r.x, mergedAntecedent,
                                inter, ruleSup, supportRatio, confidence, lift);
                        rules.add(rule);
                        if (Precision.compareTo(confidence, minConf, 0.0001) >= 0
                                && supportRatio >= minSupRatio) {
                            addToOutputRules(new Rule(rule));
                        }
                    }
                }
                if (ys.size() == level + 1 - r.y.size()) {
                    BitSet inter = new BitSet();
                    inter.or(ys.get(0).transactions);
                    for (int i1 = 1; i1 < ys.size(); i1++) {
                        RuleWithTransactions rule = ys.get(i1);
                        inter.and(rule.transactions);
                    }

                    double ruleSup = inter.cardinality() / noTransactions;
                    if (ruleSup >= minSup) {
                        double supportRatio =
                                inter.cardinality() / (double) intersectingTransactions.cardinality();
                        //mergeConsequents behöver synkas
                        ItemSet mergeConsequents = mergeConsequents(ys, ys.size() - 1);
                        if (usedX.contains(mergeConsequents)) {
                            continue;
                        }
                        double ORconf = ruleSup / supports.get(mergeConsequents);
                        double lift = ruleSup / (supports.get(mergeConsequents) * supports.get(r.y));

                        RuleWithTransactions rule = new RuleWithTransactions(mergeConsequents, r.y,
                                inter, ruleSup, supportRatio, ORconf, lift);
                        rules.add(rule);
                        if (Precision.compareTo(rule.getORconf(), minConf, 0.0001) >= 0
                                && supportRatio >= minSupRatio) {
                            addToOutputRules(new Rule(rule));
                        }

                    }
                }
            }
        }

        private void extractRulesOnFirstLevel(ItemsetWithTransactions iItem, ItemsetWithTransactions jItem){

            //Level 1 rule-extraction
            List<ItemsetWithTransactions> matches2 = new ArrayList<>();
            matches2.add(iItem);
            matches2.add(jItem);
            for (int k = 0; k < matches2.size(); k++) {
                ItemsetWithTransactions kOrder = matches2.get(k);
                ItemsetWithTransactions mOrder = null;
                for (int m = 0; m < matches2.size(); m++) {
                    if (m == k) {
                        continue;
                    }
                    mOrder = matches2.get(m);
                }
                int itemA = kOrder.getItemSet().get(0);
                int itemB = mOrder.getItemSet().get(0);

                BitSet beforeIntersection = itemIntersect(orderConstraint, itemPositionMap,
                        intersectingTransactions, itemA, itemB);

                double ruleSup = beforeIntersection.cardinality() / noTransactions;
                if (ruleSup >= minSup) {
                    double supportRatio = beforeIntersection.cardinality()
                            / (double) intersectingTransactions.cardinality();
                    double ORconf = ruleSup / supports.get(kOrder.getItemSet());
                    double lift = ruleSup
                            / (supports.get(kOrder.getItemSet()) * supports.get(mOrder.getItemSet()));
                    RuleWithTransactions rule = new RuleWithTransactions(kOrder.getItemSet(),
                            mOrder.getItemSet(), beforeIntersection, ruleSup, supportRatio, ORconf, lift);
                    rules.add(rule);
                    if (Precision.compareTo(rule.getORconf(), minConf, 0.0001) >= 0
                            && supportRatio >= minSupRatio) {
                        addToOutputRules(new Rule(rule));
                    }


                }
            }
        }





    }

}