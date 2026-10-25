"use strict";

const assert = require("assert");
const {
  canAdoptSuccessor, knownGoalNames, restoredStateForDocumentText, stateWithOpenGoal,
  requestGoalLayout, requestGoalTransition, stateGoalReference,
} = require("../out/stateHistory");

function makeHistory(currentStateId, states, edges) {
  return {
    currentStateId,
    states: new Map(states.map((state) => [state.stateId, state])),
    edges,
  };
}

const root = { stateId: "root", documentText: "source" };
const first = { stateId: "first", documentText: "source + first", parentStateId: "root" };
const second = { stateId: "second", documentText: "source + first + second", parentStateId: "first" };
const history = makeHistory("second", [root, first, second], [
  { parentStateId: "root", successorStateId: "first" },
  { parentStateId: "first", successorStateId: "second" },
]);

assert.strictEqual(
  restoredStateForDocumentText(history, "source").stateId,
  "root",
  "a revert may jump to an older ancestor, not only the immediate parent"
);
assert.strictEqual(
  restoredStateForDocumentText(history, "source + first").stateId,
  "first",
  "an undo snapshot selects its matching intermediate state"
);
assert.strictEqual(
  restoredStateForDocumentText(makeHistory("root", [root, first, second], history.edges),
    "source + first + second").stateId,
  "second",
  "redo can follow a known descendant snapshot"
);
assert.strictEqual(
  restoredStateForDocumentText(history, "manual edit"),
  undefined,
  "unrecognized manual edits must not silently change the selected root"
);

const ambiguous = makeHistory("root", [
  root,
  { stateId: "branch-a", documentText: "same text", parentStateId: "root" },
  { stateId: "branch-b", documentText: "same text", parentStateId: "root" },
], [
  { parentStateId: "root", successorStateId: "branch-a" },
  { parentStateId: "root", successorStateId: "branch-b" },
]);
assert.strictEqual(
  restoredStateForDocumentText(ambiguous, "same text"),
  undefined,
  "identical sibling snapshots must not cause an arbitrary state choice"
);

const goalRoot = {
  stateId: "goal-root", documentText: "quad source",
  goals: [{ name: "quadBody", goalId: "goal-quad" }],
};
const goalDone = {
  stateId: "goal-done", documentText: "quad completed", parentStateId: "goal-root",
  goals: [{ name: "addThreeBody", goalId: "goal-add-three" }],
};
const goalHistory = makeHistory("goal-done", [goalRoot, goalDone], [
  { parentStateId: "goal-root", successorStateId: "goal-done" },
]);
assert.strictEqual(
  stateWithOpenGoal(goalHistory, "quadBody").stateId,
  "goal-root",
  "a completed goal can be reopened through its nearest known ancestor state"
);
const historicalQuad = stateGoalReference(goalHistory, "quadBody");
assert.strictEqual(historicalQuad.state.stateId, "goal-root");
assert.strictEqual(historicalQuad.goal.goalId, "goal-quad");
assert.strictEqual(
  goalHistory.currentStateId,
  "goal-done",
  "resolving a historical action reference does not change the selected root"
);
assert.strictEqual(
  canAdoptSuccessor("goal-done", "quad completed", "goal-root", "quad source"),
  false,
  "a transition from a historical root is stored without changing the selected state or editor"
);
assert.strictEqual(
  canAdoptSuccessor("goal-root", "quad source", "goal-root", "quad source"),
  true,
  "a transition can be adopted when its exact source state remains selected and displayed"
);
assert.strictEqual(
  stateWithOpenGoal(goalHistory, "addThreeBody").stateId,
  "goal-done",
  "goals still open in the selected state stay on that state"
);
assert.deepStrictEqual(
  knownGoalNames(goalHistory),
  ["quadBody", "addThreeBody"],
  "the goal picker keeps historical goals available alongside current goals"
);
assert.strictEqual(
  stateWithOpenGoal(goalHistory, "unknown"),
  undefined,
  "unknown goals are never resolved to an arbitrary state"
);

const branchedGoals = makeHistory("branch-root", [
  { stateId: "branch-root", documentText: "root", goals: [] },
  { stateId: "open-a", documentText: "a", parentStateId: "branch-root",
    goals: [{ name: "quadBody", goalId: "goal-a" }] },
  { stateId: "open-b", documentText: "b", parentStateId: "branch-root",
    goals: [{ name: "quadBody", goalId: "goal-b" }] },
], [
  { parentStateId: "branch-root", successorStateId: "open-a" },
  { parentStateId: "branch-root", successorStateId: "open-b" },
]);
assert.strictEqual(
  stateWithOpenGoal(branchedGoals, "quadBody"),
  undefined,
  "equidistant sibling states require an explicit history choice"
);

async function testHistoricalActionRequest() {
  const calls = [];
  const client = {
    async queryShedStateActions(...args) {
      calls.push(["query", ...args]);
      return { actions: [{ id: "refine" }] };
    },
    async transitionShedState(...args) {
      calls.push(["transition", ...args]);
      return { successorStateId: "quad-alternate" };
    },
  };
  const result = await requestGoalTransition(
    client, goalHistory, "file:///walkthrough.nim", "quadBody", "refine", { term: "x" }
  );
  assert.deepStrictEqual(calls, [
    ["query", "file:///walkthrough.nim", "goal-root", "goal-quad"],
    ["transition", "file:///walkthrough.nim", "goal-root", "goal-quad", "refine", { term: "x" }],
  ], "the LSP receives the exact historical state and goal IDs for both requests");
  assert.deepStrictEqual(result, { successorStateId: "quad-alternate" });
  assert.strictEqual(
    goalHistory.currentStateId,
    "goal-done",
    "querying and transitioning from history does not select the historical root"
  );

  const layoutCalls = [];
  const rendered = await requestGoalLayout({
    async shedStateLayout(...args) {
      layoutCalls.push(args);
      return { box: { holeIds: ["hole-quad"] } };
    },
  }, goalHistory, "file:///walkthrough.nim", "quadBody");
  assert.deepStrictEqual(layoutCalls, [
    ["file:///walkthrough.nim", "goal-root", "goal-quad"],
  ], "historical layout requests use the exact referenced state and goal IDs");
  assert.deepStrictEqual(rendered.layout, { box: { holeIds: ["hole-quad"] } });
  assert.strictEqual(rendered.reference.state.stateId, "goal-root");
  assert.strictEqual(
    goalHistory.currentStateId,
    "goal-done",
    "rendering a historical goal leaves the selected proof state unchanged"
  );

  const rejectingClient = {
    ...client,
    async queryShedStateActions() { return { actions: [] }; },
    async transitionShedState() { throw new Error("transition must not be called"); },
  };
  await assert.rejects(
    requestGoalTransition(
      rejectingClient, goalHistory, "file:///walkthrough.nim", "quadBody", "give", { term: "x" }
    ),
    /action 'give' is not available/
  );
}

testHistoricalActionRequest().then(() => {
  console.log("--- source snapshot history tests passed ---");
}).catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
