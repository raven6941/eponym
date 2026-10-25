/** A locally known proof-state snapshot backed by exact source text. */
export interface SourceSnapshotState {
  stateId: string;
  documentText: string;
  parentStateId?: string;
  /** Goals that can be acted on in this exact proof state. */
  goals?: readonly { name: string; goalId: string }[];
}

export interface SourceSnapshotEdge {
  parentStateId: string;
  successorStateId: string;
}

export interface SourceSnapshotHistory {
  currentStateId: string;
  states: ReadonlyMap<string, SourceSnapshotState>;
  edges: readonly SourceSnapshotEdge[];
}

export interface StateActionClient<TTransition> {
  queryShedStateActions(
    docUri: string, stateId: string, goalId: string
  ): Promise<{ actions: Array<{ id: string }> }>;
  transitionShedState(
    docUri: string, stateId: string, goalId: string, actionId: string,
    arguments_: Record<string, unknown>
  ): Promise<TTransition>;
}

export interface StateGoalLayoutClient<TLayout> {
  shedStateLayout(docUri: string, stateId: string, goalId: string): Promise<TLayout>;
}

/** Adopt a checked successor only when it was computed from the selected root
 * and the editor still displays that root's exact source snapshot. */
export function canAdoptSuccessor(
  selectedStateId: string, editorText: string,
  parentStateId: string, parentText: string
): boolean {
  return selectedStateId === parentStateId && editorText === parentText;
}

/** Goal picker choices stay available after a goal closes in the selected root. */
export function knownGoalNames(history: SourceSnapshotHistory): string[] {
  return [...new Set([...history.states.values()].flatMap((state) =>
    state.goals?.map((goal) => goal.name) ?? []
  ))];
}

/**
 * Find a known state whose source still contains a goal hole. Prefer the selected state, then
 * the nearest ancestor. If no ancestor has it, accept only a unique nearest
 * state elsewhere in the local DAG; sibling branches need an explicit choice.
 */
export function stateWithOpenGoal(
  history: SourceSnapshotHistory, goalName: string
): SourceSnapshotState | undefined {
  const current = history.states.get(history.currentStateId);
  if (!current) return undefined;
  if (current.goals?.some((goal) => goal.name === goalName)) return current;

  let parentId = current.parentStateId;
  while (parentId) {
    const parent = history.states.get(parentId);
    if (!parent) break;
    if (parent.goals?.some((goal) => goal.name === goalName)) return parent;
    parentId = parent.parentStateId;
  }

  let frontier = [history.currentStateId];
  const visited = new Set(frontier);
  while (frontier.length > 0) {
    const next: string[] = [];
    for (const stateId of frontier) {
      for (const edge of history.edges) {
        const neighbor = edge.parentStateId === stateId ? edge.successorStateId :
          edge.successorStateId === stateId ? edge.parentStateId : undefined;
        if (!neighbor || visited.has(neighbor)) continue;
        visited.add(neighbor);
        next.push(neighbor);
      }
    }
    const matches = next
      .map((stateId) => history.states.get(stateId))
      .filter((state): state is SourceSnapshotState =>
        !!state && state.goals?.some((goal) => goal.name === goalName) === true
      );
    if (matches.length === 1) return matches[0];
    if (matches.length > 1) return undefined;
    frontier = next;
  }
  return undefined;
}

/** Resolve a UI goal name to the exact state and goal identity for an LSP request. */
export function stateGoalReference(
  history: SourceSnapshotHistory, goalName: string
): { state: SourceSnapshotState; goal: { name: string; goalId: string } } | undefined {
  const state = stateWithOpenGoal(history, goalName);
  const goal = state?.goals?.find((item) => item.name === goalName);
  return state && goal ? { state, goal } : undefined;
}

/** Render a goal from its referenced open state, even when another root is selected. */
export async function requestGoalLayout<TLayout>(
  client: StateGoalLayoutClient<TLayout>, history: SourceSnapshotHistory,
  docUri: string, goalName: string
): Promise<{
  reference: { state: SourceSnapshotState; goal: { name: string; goalId: string } };
  layout: TLayout;
}> {
  const reference = stateGoalReference(history, goalName);
  if (!reference) {
    throw new Error(
      `goal '${goalName}' has no unique state reference in local history; ` +
      "select a history state that contains the unresolved goal"
    );
  }
  const layout = await client.shedStateLayout(
    docUri, reference.state.stateId, reference.goal.goalId
  );
  return { reference, layout };
}

/** Query and transition against the exact state/goal reference without selecting it. */
export async function requestGoalTransition<TTransition>(
  client: StateActionClient<TTransition>, history: SourceSnapshotHistory,
  docUri: string, goalName: string, actionId: string,
  arguments_: Record<string, unknown>
): Promise<TTransition> {
  const reference = stateGoalReference(history, goalName);
  if (!reference) {
    throw new Error(
      `goal '${goalName}' has no unique state reference in local history; ` +
      "select a history state that contains the unresolved goal"
    );
  }
  const { state, goal } = reference;
  const available = await client.queryShedStateActions(docUri, state.stateId, goal.goalId);
  if (!available.actions.some((action) => action.id === actionId)) {
    throw new Error(`action '${actionId}' is not available for shed '${goalName}'`);
  }
  return client.transitionShedState(
    docUri, state.stateId, goal.goalId, actionId, arguments_
  );
}

/**
 * Match an editor buffer restored by native Undo/Redo or File: Revert File to
 * a state on the selected branch. Prefer the nearest ancestor (undo/revert),
 * then the nearest descendant (redo). Never guess across sibling branches.
 */
export function restoredStateForDocumentText(
  history: SourceSnapshotHistory, documentText: string
): SourceSnapshotState | undefined {
  const current = history.states.get(history.currentStateId);
  if (!current || current.documentText === documentText) return undefined;

  let parentId = current.parentStateId;
  while (parentId) {
    const parent = history.states.get(parentId);
    if (!parent) break;
    if (parent.documentText === documentText) return parent;
    parentId = parent.parentStateId;
  }

  let frontier = [history.currentStateId];
  const visited = new Set(frontier);
  while (frontier.length > 0) {
    const next: string[] = [];
    for (const parentStateId of frontier) {
      for (const edge of history.edges) {
        if (edge.parentStateId !== parentStateId || visited.has(edge.successorStateId)) continue;
        visited.add(edge.successorStateId);
        next.push(edge.successorStateId);
      }
    }
    const matches = next
      .map((stateId) => history.states.get(stateId))
      .filter((state): state is SourceSnapshotState =>
        !!state && state.documentText === documentText
      );
    if (matches.length === 1) return matches[0];
    if (matches.length > 1) return undefined;
    frontier = next;
  }
  return undefined;
}
