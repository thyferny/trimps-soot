package soot.jimple.infoflow.data.pathBuilders;

import heros.solver.CountingThreadPoolExecutor;

import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.jimple.Stmt;
import soot.jimple.infoflow.InfoflowResults;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AbstractionAtSink;
import soot.jimple.infoflow.data.SourceContextAndPath;

/**
 * Class for reconstructing abstraction paths from sinks to source
 * 
 * @author Steven Arzt
 */
public class SemiThreadedPathBuilder implements IAbstractionPathBuilder {
	
	private AtomicInteger propagationCount = null;
    private final Logger logger = LoggerFactory.getLogger(getClass());

    private final InfoflowResults results = new InfoflowResults();
	private final CountingThreadPoolExecutor executor;
	
	private final Set<Abstraction> roots = Collections.newSetFromMap
			(new IdentityHashMap<Abstraction,Boolean>());
	private Map<Abstraction, Set<Abstraction>> successors = null;
	private Map<Abstraction, Set<Abstraction>> neighbors = null;
	
	private static int lastTaskId = 0;
	
	/**
	 * Creates a new instance of the {@link SemiThreadedPathBuilder} class
	 * @param maxThreadNum The maximum number of threads to use
	 */
	public SemiThreadedPathBuilder(int maxThreadNum) {
        int numThreads = Runtime.getRuntime().availableProcessors();
		this.executor = createExecutor(maxThreadNum == -1 ? numThreads
				: Math.min(maxThreadNum, numThreads));
	}
	
	/**
	 * Creates a new executor object for spawning worker threads
	 * @param numThreads The number of threads to use
	 * @return The generated executor
	 */
	private CountingThreadPoolExecutor createExecutor(int numThreads) {
		return new CountingThreadPoolExecutor
				(numThreads, Integer.MAX_VALUE, 30, TimeUnit.SECONDS,
				new LinkedBlockingQueue<Runnable>());
	}
	
	/**
	 * Task for only finding sources, not the paths towards them
	 * 
	 * @author Steven Arzt
	 */
	private class SourceFindingTask implements Runnable {
		private final int taskId;
		private final AbstractionAtSink flagAbs;
		private final List<Abstraction> abstractionQueue = new LinkedList<Abstraction>();
		
		public SourceFindingTask(int taskId, AbstractionAtSink flagAbs, Abstraction abstraction) {
			this.taskId = taskId;
			this.flagAbs = flagAbs;
			this.abstractionQueue.add(abstraction);
		}
		
		private boolean addSuccessor(Abstraction parent, Abstraction child) {
			if (successors != null) {
				synchronized (successors) {
					Set<Abstraction> succs = successors.get(parent);
					if (succs == null) {
						succs = Collections.newSetFromMap(new IdentityHashMap<Abstraction,Boolean>());
						successors.put(parent, succs);
					}
					return succs.add(child);
				}
			}
			return false;
		}
		
		private boolean addNeighbor(Abstraction abs, Abstraction neighbor) {
			if (neighbors != null) {
				synchronized (neighbors) {
					Set<Abstraction> succs = neighbors.get(abs);
					if (succs == null) {
						succs = Collections.newSetFromMap(new IdentityHashMap<Abstraction,Boolean>());
						neighbors.put(abs, succs);
					}
					return succs.add(neighbor);
				}
			}
			return false;
		}

		private void addRoot(Abstraction root) {
			if (roots != null)
				if (!roots.contains(root))	// abort early if possible
					synchronized (roots) {
						roots.add(root);
					}
		}

		@Override
		public void run() {
			while (!abstractionQueue.isEmpty()) {
				Abstraction abstraction = abstractionQueue.remove(0);
				propagationCount.incrementAndGet();
				
				if (abstraction.getPredecessor() != null)
					addSuccessor(abstraction.getPredecessor(), abstraction);
				if (abstraction.getNeighbors() != null)
					for (Abstraction nb : abstraction.getNeighbors()) {
						addNeighbor(nb, abstraction);
						addNeighbor(abstraction, nb);
					}
				
				if (abstraction.getSourceContext() != null) {
					// Register the result
					if (successors == null)
						results.addResult(flagAbs.getSinkValue(),
								flagAbs.getSinkStmt(),
								abstraction.getSourceContext().getValue(),
								abstraction.getSourceContext().getStmt(),
								abstraction.getSourceContext().getUserData(),
								Collections.<Stmt>emptyList());
					else {
						SourceContextAndPath rootScap = new SourceContextAndPath
								(abstraction.getSourceContext().getValue(),
								abstraction.getSourceContext().getStmt(),
								abstraction.getSourceContext().getUserData()).extendPath
										(abstraction.getSourceContext().getStmt());
						abstraction.getOrMakePathCache().add(rootScap);				
						addRoot(abstraction);
					}
					
					// Sources may not have predecessors
					assert abstraction.getPredecessor() == null;
				}
				else
					if (abstraction.getPredecessor().registerPathFlag(taskId))
						abstractionQueue.add(abstraction.getPredecessor());
				
				if (abstraction.getNeighbors() != null)
					for (Abstraction nb : abstraction.getNeighbors())
						if (nb.registerPathFlag(taskId))
							abstractionQueue.add(nb);
			}
		}
	}
	
	/**
	 * Task that extend paths down the data flow
	 * 
	 * @author Steven Arzt
	 */
	private class ExtendPathTask implements Runnable {
		
		private final Object flagAbs;
		private final Abstraction parent;
		
		public ExtendPathTask(Object flagAbs, Abstraction parent) {
			this.flagAbs = flagAbs;
			this.parent = parent;
		}
		
		@Override
		public void run() {
			// Check the paths of the parent. If we have none, we can abort
			Set<SourceContextAndPath> parentPaths = parent.getPaths();
			if (parentPaths == null || parentPaths.isEmpty())
				return;
				
			// Copy over the paths of our neighbors
			Set<Abstraction> nbs = neighbors.get(parent);
			if (nbs != null)
				for (Abstraction nb : nbs) {
					Set<SourceContextAndPath> nbPaths = nb.getPaths();
					if (nbPaths != null)
						parentPaths.addAll(nbPaths);
				}
				
			// Get the children. If we have none, we can abort
			Set<Abstraction> children = successors.get(parent);
			if (children == null || children.isEmpty())
				return;
				
			for (Abstraction child : children) {
				boolean added = false;
				Set<SourceContextAndPath> childScaps = child.getOrMakePathCache();
				for (SourceContextAndPath scap : parentPaths) {
					if (child.getCurrentStmt() != null) {
						SourceContextAndPath extendedScap = scap.extendPath(child.getCurrentStmt());
						if (childScaps.add(extendedScap))
							added = true;
					}
					else if (childScaps.add(scap))
						added = true;
				}
					
				// If we have added a new path, we schedule it to be propagated
				// down to the child's children
				if (added) {
					executor.execute(new ExtendPathTask(flagAbs, child));
					Set<Abstraction> childNbs = neighbors.get(child);
					if (childNbs != null)
						for (Abstraction nb : childNbs)
						executor.execute(new ExtendPathTask(flagAbs, nb));
				}
			}
		}
	}

	@Override
	public void computeTaintSources(final Set<AbstractionAtSink> res) {
		if (res.isEmpty())
			return;
		
		long beforePathTracking = System.nanoTime();
		propagationCount = new AtomicInteger();
    	logger.info("Obtainted {} connections between sources and sinks", res.size());
    	
    	// Start the propagation tasks
    	int curResIdx = 0;
    	for (final AbstractionAtSink abs : res) {
    		logger.info("Building path " + ++curResIdx);
    		executor.execute(new SourceFindingTask(lastTaskId++, abs, abs.getAbstraction()));
    	}

    	try {
			executor.awaitCompletion();
		} catch (InterruptedException ex) {
			logger.error("Could not wait for path executor completion: {0}", ex.getMessage());
			ex.printStackTrace();
		}
    	
    	logger.info("Path processing took {} seconds in total for {} edges",
    			(System.nanoTime() - beforePathTracking) / 1E9, propagationCount.get());
	}
	
	@Override
	public void computeTaintPaths(final Set<AbstractionAtSink> res) {
		if (res.isEmpty())
			return;
		
		long beforePathTracking = System.nanoTime();
		successors = new IdentityHashMap<Abstraction, Set<Abstraction>>();
		neighbors = new IdentityHashMap<Abstraction, Set<Abstraction>>();
		computeTaintSources(res);
		
    	// Start the path extensions tasks
		logger.info("Running path extension on {} roots", roots.size());
    	for (Abstraction root : roots)
   			executor.execute(new ExtendPathTask(new Object(), root));
    	
    	try {
			executor.awaitCompletion();
		} catch (InterruptedException ex) {
			logger.error("Could not wait for path executor completion: {0}", ex.getMessage());
			ex.printStackTrace();
		}
    	
    	logger.info("Path extension took {} seconds.", (System.nanoTime() - beforePathTracking) / 1E9);
    	
    	// Collect the results
    	for (final AbstractionAtSink abs : res) {
    		Set<SourceContextAndPath> allScaps = new HashSet<SourceContextAndPath>();
    		if (abs.getAbstraction().getPaths() != null)
    			allScaps.addAll(abs.getAbstraction().getPaths());
    		if (abs.getAbstraction().getNeighbors() != null)
    			for (Abstraction nb : abs.getAbstraction().getNeighbors())
    				if (nb.getPaths() != null)
    					allScaps.addAll(nb.getPaths());
    		
    		for (SourceContextAndPath context : allScaps)
				results.addResult(abs.getSinkValue(), abs.getSinkStmt(),
						context.getValue(), context.getStmt(), context.getUserData(),
						context.getPath(), abs.getSinkStmt());
    	}
    	
    	successors = null;
    	logger.info("Path proecssing took {} seconds in total", (System.nanoTime() - beforePathTracking) / 1E9);
	}
	
	@Override
	public void shutdown() {
    	executor.shutdown();		
	}

	@Override
	public InfoflowResults getResults() {
		return this.results;
	}

}
