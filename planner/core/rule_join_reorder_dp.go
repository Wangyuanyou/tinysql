// Copyright 2018 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"math/bits"
	// "github.com/pingcap/errors"
	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/parser/ast"
)

type joinReorderDPSolver struct {
	*baseSingleGroupJoinOrderSolver
	newJoin func(lChild, rChild LogicalPlan, eqConds []*expression.ScalarFunction, otherConds []expression.Expression) LogicalPlan
}

type joinGroupEqEdge struct {
	nodeIDs []int
	edge    *expression.ScalarFunction
}

type joinGroupNonEqEdge struct {
	nodeIDs    []int
	nodeIDMask uint
	expr       expression.Expression
}

func (s *joinReorderDPSolver) solve(joinGroup []LogicalPlan, eqConds []expression.Expression) (LogicalPlan, error) {
	// TODO: You need to implement the join reorder algo based on DP.

	// The pseudo code can be found in README.
	// And there's some common struct and method like `baseNodeCumCost`, `calcJoinCumCost` you can use in `rule_join_reorder.go`.
	// Also, you can take a look at `rule_join_reorder_greedy.go`, this file implement the join reorder algo based on greedy algorithm.
	// You'll see some common usages in the greedy version.

	// Note that the join tree may be disconnected. i.e. You need to consider the case `select * from t, t1, t2`.

	// This Link give a brief introduction about join reorder：https://docs.pingcap.com/tidb/stable/join-reorder

	// 1. Init curJoinGroup for JoinReorderSolver
	// a. Derive the stats information recursively on every node 
	//    I think that this step is a prerequisite for  calculating cumulative join cost
	//    cumulative join cost = CumCount(lhs) + CumCount(rhs) + RowCount(join)
	//       For base node, its CumCount equals to the sum of the count of its subtree.
	//       See baseNodeCumCost for more details.
	// b. init curJoinGroup for JoinReorderSolver
	//   curJoinGroup is a list of all table and node's CumCost

	for _, node := range joinGroup {
		_, err := node.recursiveDeriveStats()
		if err != nil {
			return nil, err
		}
		// Each entry is a logical plan with associated cost
		s.curJoinGroup = append(s.curJoinGroup, &jrNode{
			p:       node,
			cumCost: s.baseNodeCumCost(node),
		})
	}

	//2. Build Graph(connection) for nodes according to eqConds
	//  a. Design data structure for graph
	//    adjacents: a mapping from node(index in curJoinGroup) to a list of connecting node, notice: the edges here are bidirectional
	//    eqEdges: a list of joinGroupEqEdge. joinGroupEqEdge = 2 endpoints + condition expression
	adjacents := make([][]int, len(s.curJoinGroup))
	eqEdges := make([]joinGroupEqEdge, 0, len(eqConds))

	//  b. Traverse eqConds and initialize adjacents and totalEqEdges
	for _, cond := range eqConds {
		eqFunc := cond.(*expression.ScalarFunction)
		eqFuncArgs := eqFunc.GetArgs()
		eqColL := eqFuncArgs[0].(*expression.Column)
		eqColR := eqFuncArgs[1].(*expression.Column)
		// find the index in joinGroup for a Node ( or Col)
		// the the index in joinGroup is equal to the index in s.curJoinGroup
		eqIdxL, err := findNodeIndexInGroup(joinGroup, eqColL)
		if err != nil {
			return nil, err
		}
		eqIdxR, err := findNodeIndexInGroup(joinGroup, eqColR)
		if err != nil {
			return nil, err
		}

		adjacents[eqIdxL] = append(adjacents[eqIdxL], eqIdxR)
		adjacents[eqIdxR] = append(adjacents[eqIdxR], eqIdxL)
		eqEdges = append(eqEdges, joinGroupEqEdge{
			nodeIDs: []int{eqIdxL, eqIdxR},
			edge:    eqFunc,
		})
	}

	//3. Init nonEqEdges 
	nonEqEdges := make([]joinGroupNonEqEdge, 0, len(s.otherConds))
	for _, cond := range s.otherConds {
		cols := expression.ExtractColumns(cond)
		mask := uint(0)
		ids := make([]int, 0, len(cols))
		for _, col := range cols {
			idx, err := findNodeIndexInGroup(joinGroup, col)
			if err != nil {
				return nil, err
			}
			ids = append(ids, idx)
			mask |= 1 << uint(idx)
		}
		nonEqEdges = append(nonEqEdges, joinGroupNonEqEdge{
			// joinGroupNonEqEdge contains details information about one nonEqEdge
			// A nonEqEdge may contains multiple cols(an eq condition only contains 2 cols, left col + right col)
			//   i.  nodeIDs: all cols indexes in joinGroup
			//   ii. nodeIDMask: represent nodeIDs via bitmap, if ith in nodeIDs, nodeIDMask&(1 << ith) != 0
			//   iii. expr: cond expression 
			nodeIDs:    ids,  
			nodeIDMask: mask,
			expr:       cond,
		})
	}

	//4. Find all connected components and do DP in every compontts
	//   a. init data structs in forest scope (joinGroup is a forest, every connected component is a tree)
	//       visiteds: record for every element in joinGroup. it record if this node has been visisted, which will be used during fining connected components(bfs)
	//       forest2TreeInx: a map from node's forest index to index in its tree.
	//       remainedJoins: after found best plan for every tree, we will got a lists of join(a join per tree). It will be finally used to do  cartesian joins
	visiteds := make([]bool, len(joinGroup))
	forest2TreeInx := make([]int, len(joinGroup))
	var remainedJoins []LogicalPlan 

	for i := 0; i < len(joinGroup); i++ {
		if visiteds[i] {
			continue
		}
		// For every non-visisted node, use BFS to build Connected Component for it
		// tree2ForestInx has two meanings:
		//  1. it is a list of all node index(index in forest) in current Connected Component
		//  2. it is also a mapping from tree index to forest index
		tree2ForestInx := s.buildConnectedComponentBFS(i, visiteds, adjacents, forest2TreeInx)
		
		// build a bit map which marks the node in current Connected Component
		connCompMask := uint(0)
		for _, inxInForest := range tree2ForestInx {
			connCompMask |= 1 << uint(inxInForest)
		}

		// extract this Connected Component nonEqEdges from nonEqEdges ( which stores all nonEqEdges in forest)
		var connCompNonEqEdges []joinGroupNonEqEdge
		for i := len(nonEqEdges) - 1; i >= 0; i-- {
			curNonEqEdge := nonEqEdges[i]
			if curNonEqEdge.nodeIDMask&connCompMask != curNonEqEdge.nodeIDMask {
				// this branch means that nonEqEdges[i] does not contain all nodes in current Connected Component
				continue
			}
			
			// Passing above conditional, nonEqEdges[i] can be a nonEqEdges for current connected componet 
			// build nodeIDMask of nonEqEdges[i], notice!: to build this mask, we need to build according to node' inx in connected componet(tree)
			// build new mask for it  +  remove it from nonEqEdges + add it into connCompNonEqEdges
			curNonEdgeMaskInConnComp := uint(0)
			for _, inxInForest := range curNonEqEdge.nodeIDs {
				curNonEdgeMaskInConnComp |= 1 << uint(forest2TreeInx[inxInForest])
			}
			curNonEqEdge.nodeIDMask = curNonEdgeMaskInConnComp
			connCompNonEqEdges = append(connCompNonEqEdges, curNonEqEdge)
			nonEqEdges = append(nonEqEdges[:i], nonEqEdges[i+1:]...)
		}

		//Do DP to find best plan for this Connected Component.
		//You will get one final join logicplan for one Connected Component
		join, err := s.findBestPlanViaDP(tree2ForestInx, forest2TreeInx, joinGroup, eqEdges, connCompNonEqEdges)
		if err != nil {
			return nil, err
		}
		remainedJoins = append(remainedJoins, join)
	}

	// build otherConditions for last step cartesian joins
	remainedOtherConds := make([]expression.Expression, 0, len(nonEqEdges))
	for _, edge := range nonEqEdges {
		remainedOtherConds = append(remainedOtherConds, edge.expr)
	}
	return s.makeBushyJoin(remainedJoins, remainedOtherConds), nil
}




// buildConnectedComponentBFS 
// find all nodes in current connected components via bfs.
// return value has two meanings:
//    1. it is a list of all node index(index in forest) in current Connected Component
//    2. it is also a mapping from tree index to forest index
func (s *joinReorderDPSolver) buildConnectedComponentBFS(startNode int, visiteds []bool, adjacents [][]int, forest2TreeInx []int) []int {
	queue := []int{startNode}
	visiteds[startNode] = true
	var tree2ForestInx []int
	for len(queue) > 0 {
		// visist the head of queue and pop it out 
		curForestInx := queue[0]
		queue = queue[1:]

		// update 2 maps 
		forest2TreeInx[curForestInx] = len(tree2ForestInx)
		tree2ForestInx = append(tree2ForestInx, curForestInx)

		// add the son of curForestInx into queue
		for _, adjForestInx := range adjacents[curForestInx] {
			if visiteds[adjForestInx] {
				continue
			}
			queue = append(queue, adjForestInx)
			visiteds[adjForestInx] = true
		}
	}
	return tree2ForestInx
}

// findBestPlanViaDP is the core part of this algorithm.
// It implements join reorder algorithm: DP by subset using the following formula:
//   bestPlan[S:set of node] = the best one among Join(bestPlan[S1:subset of S], bestPlan[S2: S/S1])
func (s *joinReorderDPSolver) findBestPlanViaDP(tree2ForestInx, forest2TreeInx []int, joinGroup []LogicalPlan,
	eqEdges []joinGroupEqEdge, nonEqEdges []joinGroupNonEqEdge) (LogicalPlan, error) {
	nodeCnt := uint(len(tree2ForestInx))

	//bestPlan is the dp table, which will save optimal result of all sub problems
	//bestPlan is list of jrNode.Index is bit map which represent the logic plan nodes in this jrNode
	// For example,  bestPlan[00000011] store the optimal result for a jrNode containing node 1 and node 2 
	// For example,  bestPlan[00000101] store the optimal result for a jrNode containing node 1 and node 3 
	bestPlan := make([]*jrNode, 1<<nodeCnt)
	for i := uint(0); i < nodeCnt; i++ {
		// init the Dp table
		// if jrNode only contains one node, the bestplan is the node's self
		bestPlan[1<<i] = s.curJoinGroup[tree2ForestInx[i]]
	}

	// Enumerate the nodeBitmap from small to big, make sure that S1 must be enumerated before S2 if S1 belongs to S2.
	for containBitmap := uint(1); containBitmap < (1 << nodeCnt); containBitmap++ {
		if bits.OnesCount(containBitmap) == 1 {
			// OnesCount == 1
			// means we alread find optimal result for the jrNodes which only contains one node
			// bestPlan[1<<i] = s.curJoinGroup[tree2ForestInx[i]]
			continue
		}


		// This loop can iterate all its subset. 
		// All bit map from 1 to containBitmap-1 are sub problem for containBitmap
		for leftSub := (containBitmap - 1) & containBitmap; leftSub > 0; leftSub = (leftSub - 1) & containBitmap {
			rightSub := containBitmap ^ leftSub

			if leftSub > rightSub {
				// since the order of leftSub and rightSub doesn't matter 
				// so we only need visit  the pair (leftSub, rightSub) once
				continue
			}


			// If this subset is not connected skip it.
			// leftSub or rightSub is not a valid sub problem -> skip it
			if bestPlan[leftSub] == nil || bestPlan[rightSub] == nil {
				continue
			}


			// Get the connectEdges and otherConds which will be used to connect(join) leftSub and rightSub
			connectEqEdges, otherConds := s.nodesAreConnected(leftSub, rightSub, forest2TreeInx, eqEdges, nonEqEdges)

			// Here we only check equal condition currently.
			if len(connectEqEdges) == 0 {
				// if no connect edge, it means leftSub and rightSub sub problem can build a current optimal problem
				continue
			}

			// join leftSub and rightSub + create a new join plan for this 
			join, err := s.newJoinWithEdge(bestPlan[leftSub].p, bestPlan[rightSub].p, connectEqEdges, otherConds)
			if err != nil {
				return nil, err
			}

			// calculate the Cum Cost for this Join plan 
			curCost := s.calcJoinCumCost(join, bestPlan[leftSub], bestPlan[rightSub])

			// update the bestPlan[containBitmap]
			/// notice: our optimal problem is min cost problem
			if bestPlan[containBitmap] == nil {
				bestPlan[containBitmap] = &jrNode{
					p:       join,
					cumCost: curCost,
				}
			} else if bestPlan[containBitmap].cumCost > curCost {
				bestPlan[containBitmap].p = join
				bestPlan[containBitmap].cumCost = curCost
			}
		}
	}
	return bestPlan[(1<<nodeCnt)-1].p, nil
}

func (s *joinReorderDPSolver) nodesAreConnected(leftMask, rightMask uint, forest2TreeInx []int,
	eqEdges []joinGroupEqEdge, nonEqEdges []joinGroupNonEqEdge) ([]joinGroupEqEdge, []expression.Expression) {
	
	var (
		connectEqEdges []joinGroupEqEdge
		otherConds  []expression.Expression
	)

	// find all connectEqEdges from eqEdges
	for _, edge := range eqEdges {
		lIdx := uint(forest2TreeInx[edge.nodeIDs[0]])
		rIdx := uint(forest2TreeInx[edge.nodeIDs[1]])
		if ((leftMask&(1<<lIdx)) > 0 && (rightMask&(1<<rIdx)) > 0) || ((leftMask&(1<<rIdx)) > 0 && (rightMask&(1<<lIdx)) > 0) {
			// if lIdx in leftMask and rIdx in rightMask (or rIdx in leftMask and lIdx in rightMask)
			// it means it is connecting eq edge 
			connectEqEdges = append(connectEqEdges, edge)
		}
	}


	// find all otherConds from nonEqEdges
	for _, edge := range nonEqEdges {
		// If the result is false, means that the current group hasn't covered the columns involved in the expression.
		if edge.nodeIDMask&(leftMask|rightMask) != edge.nodeIDMask {
			continue
		}
		// Check whether this expression is only built from one side of the join.
		if edge.nodeIDMask&leftMask == 0 || edge.nodeIDMask&rightMask == 0 {
			continue
		}
		otherConds = append(otherConds, edge.expr)
	}
	return connectEqEdges, otherConds
}


func (s *joinReorderDPSolver) newJoinWithEdge(leftPlan, rightPlan LogicalPlan, edges []joinGroupEqEdge, otherConds []expression.Expression) (LogicalPlan, error) {
	var eqConds []*expression.ScalarFunction
	for _, edge := range edges {
		lCol := edge.edge.GetArgs()[0].(*expression.Column)
		rCol := edge.edge.GetArgs()[1].(*expression.Column)
		if leftPlan.Schema().Contains(lCol) {
			eqConds = append(eqConds, edge.edge)
		} else {
			newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(), rCol, lCol).(*expression.ScalarFunction)
			eqConds = append(eqConds, newSf)
		}
	}
	join := s.newJoin(leftPlan, rightPlan, eqConds, otherConds)
	_, err := join.recursiveDeriveStats()
	return join, err
}

// Make cartesian join as bushy tree.
func (s *joinReorderDPSolver) makeBushyJoin(cartesianJoinGroup []LogicalPlan, otherConds []expression.Expression) LogicalPlan {
	for len(cartesianJoinGroup) > 1 {
		resultJoinGroup := make([]LogicalPlan, 0, len(cartesianJoinGroup))
		for i := 0; i < len(cartesianJoinGroup); i += 2 {
			if i+1 == len(cartesianJoinGroup) {
				resultJoinGroup = append(resultJoinGroup, cartesianJoinGroup[i])
				break
			}
			// TODO:Since the other condition may involve more than two tables, e.g. t1.a = t2.b+t3.c.
			//  So We'll need a extra stage to deal with it.
			// Currently, we just add it when building cartesianJoinGroup.
			mergedSchema := expression.MergeSchema(cartesianJoinGroup[i].Schema(), cartesianJoinGroup[i+1].Schema())
			var usedOtherConds []expression.Expression
			otherConds, usedOtherConds = expression.FilterOutInPlace(otherConds, func(expr expression.Expression) bool {
				return expression.ExprFromSchema(expr, mergedSchema)
			})
			resultJoinGroup = append(resultJoinGroup, s.newJoin(cartesianJoinGroup[i], cartesianJoinGroup[i+1], nil, usedOtherConds))
		}
		cartesianJoinGroup = resultJoinGroup
	}
	return cartesianJoinGroup[0]
}

func findNodeIndexInGroup(group []LogicalPlan, col *expression.Column) (int, error) {
	for i, plan := range group {
		if plan.Schema().Contains(col) {
			return i, nil
		}
	}
	return -1, ErrUnknownColumn.GenWithStackByArgs(col, "JOIN REORDER RULE")
}
