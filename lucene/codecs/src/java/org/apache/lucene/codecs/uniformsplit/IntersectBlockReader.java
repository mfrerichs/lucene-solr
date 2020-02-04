/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.lucene.codecs.uniformsplit;

import java.io.IOException;

import org.apache.lucene.codecs.PostingsReaderBase;
import org.apache.lucene.index.TermState;
import org.apache.lucene.index.TermsEnum;
import org.apache.lucene.store.IndexInput;
import org.apache.lucene.util.ArrayUtil;
import org.apache.lucene.util.BytesRef;
import org.apache.lucene.util.RamUsageEstimator;
import org.apache.lucene.util.StringHelper;
import org.apache.lucene.util.automaton.Automaton;
import org.apache.lucene.util.automaton.ByteRunAutomaton;
import org.apache.lucene.util.automaton.CompiledAutomaton;
import org.apache.lucene.util.automaton.Operations;
import org.apache.lucene.util.automaton.Transition;
import org.apache.lucene.util.fst.FST;
import org.apache.lucene.util.fst.Outputs;

/**
 * The "intersect" {@link TermsEnum} response to {@link UniformSplitTerms#intersect(CompiledAutomaton, BytesRef)},
 * intersecting the terms with an automaton.
 *
 * @lucene.experimental
 */
public class IntersectBlockReader extends BlockReader {

  /*
  TODO

  - run all lucene tests to validate isDestAccepted fix
  - count number of previous blocks opened
  - count number of ceil blocks opened
  - maybe we could compute the common prefix based on previous arc and current arc before really opening a previous block.
   */

  private static final int AUTOMATON_INITIAL_STATE = 0;
  private static final BytesRef EMPTY_BYTES_REF = new BytesRef();
  private static final BytesRef ZERO_BYTES_REF = new BytesRef(new byte[] {0}, 0, 1);

  public static boolean debug = false;//nocommit
  private static final boolean UTF8_TO_STRING = true;

  private final Automaton automaton;
  private final ByteRunAutomaton runAutomaton;
  private final BytesRef commonPrefix;//nocommit
  private final BytesRef commonSuffix;
  private final FST<Long> fst;
  private final FST.BytesReader fstReader;
  private final Outputs<Long> outputs;

  private Node[] branchNodes;
  private int branchDepth;
  private final MatchResult matchResult;
  private boolean shouldScanBlock;
  private boolean scanPreviousBlock;
  private long endBlockFP;
  private int[] matchStates;
  private int matchIndex;
  private int commonPrefixIndex;
  private final FST.Arc<Long> lastSkippedArc;
  private Long lastSkippedArcOutput;
  private final FST.Arc<Long> scratchArc;
  private boolean returnStartTermOnce;
  private boolean firstBlockOpened;

  private static long constructorCallCount;

  public IntersectBlockReader(CompiledAutomaton compiled, BytesRef startTerm,
                              FSTDictionary.Supplier dictionarySupplier, IndexInput blockInput, PostingsReaderBase postingsReader,
                              FieldMetadata fieldMetadata, BlockDecoder blockDecoder) throws IOException {
    super(dictionarySupplier, blockInput, postingsReader, fieldMetadata, blockDecoder);
    constructorCallCount++;//nocommit
//    System.out.println("constructorCallCount=" + constructorCallCount);
    if (constructorCallCount == 41) {//nocommit
//      debug = true;
    } else {
      debug = false;
    }
    this.automaton = compiled.automaton;
    runAutomaton = compiled.runAutomaton;
    commonSuffix = compiled.commonSuffixRef == null ? null : (compiled.commonSuffixRef.offset == 0 ? compiled.commonSuffixRef : BytesRef.deepCopyOf(compiled.commonSuffixRef));
    commonPrefix = Operations.getCommonPrefixBytesRef(automaton);
    fst = dictionarySupplier.get().fst;
    fstReader = fst.getBytesReader();
    outputs = fst.outputs;
    branchNodes = new Node[16];
    branchDepth = -1;
    matchResult = new MatchResult();
    endBlockFP = -1;
    matchStates = new int[32];
    lastSkippedArc = new FST.Arc<>();
    scratchArc = new FST.Arc<>();
    if (debug) System.out.println("new " + IntersectBlockReader.class.getSimpleName());
    Node root = stackNode().asRoot();
    boolean startAtFirstTerm = root.transitionCount > 0 && runAutomaton.isAccept(root.transition.source);
    if (startTerm != null || startAtFirstTerm) {
      seekStartTerm(startTerm);
    }
  }

  @Override
  public BytesRef next() throws IOException {
    clearTermState();

    nodeLoop:
    while (true) {

      // If we are currently scanning a term block, continue scanning.
      if (shouldScanBlock) {
        BytesRef term = findNextMatchingTermInBlock();
        if (term != null) {
          return term;
        }
        shouldScanBlock = false;
      }

      // Pop from the stack the nodes with exhausted arc or transition iteration.
      Node node = getCurrentNode();
      while (true) {
        if (node.isArcIterationOver()) {
          if (debug) System.out.println("pop node [" + node.depth + "]");
          node = popNode();
          if (node == null) {
            // End of enumeration.
            return null;
          }
        } else if (node.isTransitionIterationOver()) {
          if (followRemainingArcs(node)) {
            continue nodeLoop;
          }
        } else {
          break;
        }
      }

      // If we only need to scan the floor and/or ceil term blocks of the sub-branch.
      if (node.onlyFloorOrCeil) {
        followFloorOrCeilArcs(node);
        continue;
      }

      // Iterate the FST arcs of the current node (the top node in the stack).
      do {
        if (iterateMatchingTransitions(node)) {
          followArc(node);
          break;
        }
        if (debug) System.out.println("[" + node.depth + "] no transitions match arc " + node.toString(node.arc));
        if (node.isTransitionIterationOver()) {
          if (debug) System.out.println("[" + node.depth + "] no more transitions");
          break;
        }
        recordLastSkippedArc(node);
      } while (node.nextArc());
    }
  }

  private enum SeekStartOption {REGULAR, AT_FIRST_TERM, AFTER_EMPTY_TERM}

  private void seekStartTerm(BytesRef startTerm) throws IOException {
    SeekStartOption seekStartOption;
    if (startTerm == null) {
      seekStartOption = SeekStartOption.AT_FIRST_TERM;
      startTerm = ZERO_BYTES_REF;
    } else if (startTerm.length == 0) {
      seekStartOption = SeekStartOption.AFTER_EMPTY_TERM;
      startTerm = ZERO_BYTES_REF;
    } else {
      seekStartOption = SeekStartOption.REGULAR;
    }
    if (debug) System.out.println("seek start term \"" + (UTF8_TO_STRING ? startTerm.utf8ToString() : startTerm) + "\"" + (seekStartOption == SeekStartOption.REGULAR ? "" : " " + seekStartOption));
    Node node = getCurrentNode();
    int startTermIndex = startTerm.offset;
    int startTermEnd = startTerm.offset + startTerm.length;
    while (true) {
      assert branchDepth == startTermIndex - startTerm.offset;
      assert node == getCurrentNode();

      if (node.arc.label() == FST.END_LABEL && node.isLastArc()) {
        // Open the term block.
        node.nextArc();
        assert node.isArcIterationOver();
        long blockFP = outputs.add(node.output, node.arc.output());
        findStartTermInBlock(node, blockFP, startTerm, seekStartOption);
        return;
      }
      int startTermLabel = startTerm.bytes[startTermIndex] & 0xFF;
      if (fst.findTargetArc(startTermLabel, node.followArc, node.arc, fstReader) == null) {
        // No match. Find floor block.
        break;
      }
      // Match. Follow the arc.
      node.setNextArc(false);
      int destState = node.setTransitionForLabel(startTermLabel);
      if (destState == -1) {
        if (seekStartOption == SeekStartOption.REGULAR) {
          throw new IllegalArgumentException("startTerm \"" + (UTF8_TO_STRING ? startTerm.utf8ToString() : startTerm) + "\" must be accepted by the automaton");
        } else {
          destState = node.transition.dest;
        }
      }
      boolean ceilMatch = node.isLastArc() && node.requiresCeilMatch
          || node.transition.max > startTermLabel
          || node.nextTransition() && (node.isLastArc() || node.transition.min < node.nextArc.label());
      matchResult.reset(destState, false, ceilMatch);
      Node nextNode = stackNode().follow(node, matchResult);
      node.nextArc(); // Prepare the next arc when later the node is poped.
      node = nextNode;
      if (++startTermIndex == startTermEnd) {
        // End of the start term but the FST branch is longer. Find floor block.
        // Create an artificial start term by appending a 0 suffix.
        // This will match a final floor arc on the node if there is one.
        byte[] bytes = new byte[startTerm.length + 1];
        System.arraycopy(startTerm.bytes, startTerm.offset, bytes, 0, startTerm.length);
        startTerm = new BytesRef(bytes, 0, bytes.length);
        break;
      }
    }
    // Find floor block.
    while (node != null) {
      assert branchDepth == startTermIndex - startTerm.offset;
      assert node == getCurrentNode();

      // Find backward the first node with first arc label < start term label.
      int startTermLabel = startTerm.bytes[startTermIndex] & 0xFF;
      fst.readFirstTargetArc(node.followArc, node.arc, fstReader);
      if (node.arc.label() < startTermLabel) {
        // Then find the max arc with label < start term label.
        boolean isFirstArc = true;
        while (!node.isLastArc() && fst.readNextArcLabel(node.arc, fstReader) < startTermLabel) {
          fst.readNextArc(node.arc, fstReader);
          isFirstArc = false;
        }
        node.setNextArc(isFirstArc);
        if (startTermIndex != startTermEnd && seekStartOption == SeekStartOption.REGULAR) { // Skip artificial 0 suffix or 0 byte for special option.
          node.setTransitionForLabel(startTermLabel);
        }
        // Then follow the ceil arcs to open the term block.
        long ceilBlockFP = getCeilBlockFP(scratchArc.copyFrom(node.arc), node.output);
        node.nextArc(); // Prepare the next arc when later the node is poped.
        findStartTermInBlock(node, ceilBlockFP, startTerm, seekStartOption);
        return;
      }
      node = popNode();
      startTermIndex--;
    }
    if (debug) System.out.println("start term before first");
    stackNode().asRoot();
  }

  private void findStartTermInBlock(Node node, long blockFP, BytesRef startTerm, SeekStartOption seekStartOption) throws IOException {
    if (seekStartOption == SeekStartOption.AT_FIRST_TERM) {
        startTerm = EMPTY_BYTES_REF;
    }
    SeekStatus seekStatus = seekInBlock(startTerm, blockFP);
    if (debug) System.out.println("seek in block FP=" + blockFP + " status=" + seekStatus);
    switch (seekStatus) {
      case FOUND:
        if (seekStartOption != SeekStartOption.REGULAR) {
          // For SeekStartOption.AT_FIRST_TERM we searched [] so we have to return it once.
          // For SeekStartOption.AFTER_EMPTY_TERM we searched [0] so we have to return it once.
          returnStartTermOnce = true;
        }
        break;
      case NOT_FOUND:
        BytesRef term = term();
        if (runAutomaton.run(term.bytes, term.offset, term.length)) {
          // The block line is positioned on the next term which is accepted by the automaton, so we have to return it once.
          returnStartTermOnce = true;
        }
        if (debug) System.out.println("positioned on term \"" + term.utf8ToString() + "\"" + (returnStartTermOnce ? " return start term once" : ""));
        break;
      case END:
        return;
      default:
        throw new IllegalStateException("Unsupported " + SeekStatus.class.getSimpleName() + " " + seekStatus);
    }
    shouldScanBlock = true;
    this.endBlockFP = blockFP;
    setCommonPrefix(node);
  }

  private boolean atLeastOneTermAcceptedInBlock;//nocommit
  private boolean atLeastOneCommonPrefixAcceptedInBlock;
  public static volatile long numBlocksOpened;
  public static volatile long numBlocksFullyRejected;
  public static volatile long numBlocksCommonPrefixNeverMatches;
  private boolean firstBlockOpened_;

  private String transitionsToString() {
    StringBuilder builder = new StringBuilder();
    transitionsToString(0, "", builder);
    return builder.toString();
  }

  private void transitionsToString(int state, String indent, StringBuilder builder) {
    Transition t = new Transition();
    int numT = automaton.initTransition(state, t);
    for (int i = 0; i < numT; i++) {
      automaton.getNextTransition(t);
      builder.append('\n').append(indent).append(t);
      transitionsToString(t.dest, indent + " ", builder);
    }
  }

  private BytesRef findNextMatchingTermInBlock() throws IOException {
    assert blockHeader != null;
    if (returnStartTermOnce) {
      returnStartTermOnce = false;
      return term();
    }
    termLoop:
    while (true) {
      if (readLineInBlock() == null) {
        // No more lines in the block.

        synchronized (IntersectBlockReader.class) {//nocommit
          numBlocksOpened++;
          if (firstBlockOpened_) {
            if (!atLeastOneTermAcceptedInBlock) {
              numBlocksFullyRejected++;
            }
            if (!atLeastOneCommonPrefixAcceptedInBlock) {
              if (debug) {
                System.out.println("commonPrefix=" + commonPrefix.utf8ToString());
                System.out.println(transitionsToString());
              }
              numBlocksCommonPrefixNeverMatches++;
            }
          } else {
            firstBlockOpened_ = true;
          }
        }
        atLeastOneTermAcceptedInBlock = false;
        atLeastOneCommonPrefixAcceptedInBlock = false;

        matchIndex = 0;
        long blockFP = blockInput.getFilePointer();
        if (blockFP > endBlockFP) {
          // Exit either if we completed the single block to read, or the last block of the series.
          scanPreviousBlock = false;
          if (debug) System.out.println("end of block");
          return null;
        }
        if (scanPreviousBlock) {
          scanPreviousBlock = false;
          setCommonPrefix(getCurrentNode());
        }
        // Scan the next block starting at the current file pointer in the block file.
        if (debug) System.out.println("open next block FP=" + blockFP);
        initializeHeader(null, blockFP);
        if (blockHeader == null) {
          throw newCorruptIndexException("Illegal absence of block", blockFP);
        }
        readLineInBlock();
      }
      TermBytes termBytes = blockLine.getTermBytes();
      BytesRef term = termBytes.term;
      byte[] bytes = term.bytes;
      assert term.offset == 0;
      int length = term.length;

      if (StringHelper.startsWith(term, commonPrefix)) {
        atLeastOneCommonPrefixAcceptedInBlock = true;
      }

      matchIndex = Math.max(Math.min(termBytes.getSuffixOffset(), matchIndex), commonPrefixIndex);
      if (commonSuffix != null) {
        int suffixLength = commonSuffix.length;
        int offset = length - suffixLength;
        if (offset < 0) {
          continue;
        }
        byte[] suffixBytes = commonSuffix.bytes;
        for (int i = 0; i < suffixLength; i++) {
          if (bytes[offset + i] != suffixBytes[i]) {
            continue termLoop;
          }
        }
      }
      int state = matchStates[matchIndex];
      while (matchIndex < length) {
        state = runAutomaton.step(state, bytes[matchIndex] & 0xff);
        if (state == -1) {
          // No match.
          if (debug) System.out.println("reject \"" + (UTF8_TO_STRING ? term.utf8ToString() : term) + "\"");
          continue termLoop;
        }
        if (++matchIndex == matchStates.length) {
          matchStates = ArrayUtil.growExact(matchStates, ArrayUtil.oversize(matchStates.length + 1, Byte.BYTES));
        }
        matchStates[matchIndex] = state;
      }
      if (runAutomaton.isAccept(state)) {
        // Match.
        if (debug) System.out.println("accept \"" + (UTF8_TO_STRING ? term.utf8ToString() : term) + "\"");
        atLeastOneTermAcceptedInBlock = true;
        return term;
      }
      // No match.
      if (debug) System.out.println("reject \"" + (UTF8_TO_STRING ? term.utf8ToString() : term) + "\"");
    }
  }

  private boolean iterateMatchingTransitions(Node node) {
    assert !node.isArcIterationOver() && !node.isTransitionIterationOver();
    int arcLabel = node.arc.label();
    int nextArcLabel;
    boolean ceilMatch;
    if (node.isLastArc()) {
      nextArcLabel = Integer.MAX_VALUE;
      ceilMatch = node.requiresCeilMatch;
    } else {
      nextArcLabel = node.nextArc.label();
      ceilMatch = false;
    }
    if (debug) System.out.println("[" + node.depth + "] iterate arc=" + node.toString(node.arc) + " nextArc=" + (nextArcLabel == Integer.MAX_VALUE ? "-" : node.toString(node.nextArc)));

    // Special case of no transitions which can accept a first final arc and floor match.
    if (node.drainNoTransitionState()) {
      if (debug) System.out.println("node has no transition");
      return matchResult.reset(-1, node.isFirstArc(), ceilMatch);
    }
    boolean floorMatchIfFirstArc = node.requiresFloorMatch;

    // Skip all transitions before the arc label.
    while (node.transition.max < arcLabel) {
      floorMatchIfFirstArc = true;
      if (!node.nextTransition()) {
        if (debug) System.out.println("skipped all transitions");
        return matchResult.reset(-1, node.isFirstArc(), ceilMatch);
      }
    }

    // Iterate the transitions matching this arc.
    // Find if there is:
    // - A transition matching exactly the arc label (transition.min <= arcLabel <= transition.max).
    // - One or more transitions ceil matching the arc (transition.min < nextArcLabel && transition.max > arcLabel).
    int exactMatchState = -1;
    boolean destinationAccepted = false;
    int min;
    while ((min = node.transition.min) < nextArcLabel) {
      if (min <= arcLabel) {
        exactMatchState = node.transition.dest;
        destinationAccepted = runAutomaton.isAccept(exactMatchState);
        if (min < arcLabel) {
          floorMatchIfFirstArc = true;
        }
        if (ceilMatch || node.transition.max > arcLabel) {
          if (exactMatchState == node.transition.source && min == 0 && node.transition.max == 255) {
            // Special case of wildcard suffix detected (e.g. PrefixQuery automaton).
            return matchResult.resetForWildcard(floorMatchIfFirstArc);
          }
          ceilMatch = true;
          break;
        }
      } else {
        ceilMatch = true;
        break;
      }
      if (!node.nextTransition()) {
        break;
      }
    }
    boolean floorMatch = destinationAccepted || floorMatchIfFirstArc && node.isFirstArc();
    return matchResult.reset(exactMatchState, floorMatch, ceilMatch);
  }

  /**
   * Follows the current {@link FST.Arc} of the provided node and advances the matching {@link Transition}
   * in case of exact match. Either stacks a new non-final node, or opens a term block for scanning (final node).
   * Also prepares the next arc of the current node, to continue the iteration from it when we finish the visit of
   * the stacked node / block scan.
   */
  private void followArc(Node node) throws IOException {
    if (node.arc.label() == FST.END_LABEL) {
      // Final node. Open the corresponding term block to prepare to scan it.
      if (debug) System.out.println("[" + node.depth + "] follow final arc");
      long blockFP = outputs.add(node.output, node.arc.output());
      openBlocks(node, maybePreviousBlockFP(node, blockFP), blockFP);
      node.nextArc(); // Continue the iteration from the next arc when we pop back this node from the stack.
    } else if (matchResult.wildcardSuffix) {
      if (debug) System.out.println("[" + node.depth + "] follow wildcard suffix");
      matchResult.wildcardSuffix = false;
      node.requiresFloorMatch = matchResult.floorMatch;
      node.requiresCeilMatch = false;
      openAllSubBlocks(node);
      node.exhaustArcIteration(); // Exhaust this node arcs (no remaining arcs to follow/skip).
    } else {
      // Non-leaf node. Advance deeper in the FST tree, stack the child node.
      if (debug) System.out.println("[" + node.depth + "] follow " + node.toString(node.arc) + " " + matchResult + " node.output=" + node.output + " arc.output=" + node.arc.output());
      stackNode().follow(node, matchResult);
      node.nextArc(); // Continue the iteration from the next arc when we pop back this node from the stack.
    }
  }

  private boolean followRemainingArcs(Node node) throws IOException {
    if (debug) System.out.println("[" + node.depth + "] follow remaining arcs");
    boolean followed = false;
    boolean floorMatch = node.requiresFloorMatch && !node.onlyFloorOrCeil && node.isFirstArc();
    if (floorMatch && !node.requiresCeilMatch) {
      // The iteration is on the first arc. Follow the floor arcs directly without reading the first arc again.
      followFloorArcs(node, true);
      followed = true;
    }
    node.jumpToLastArc();
    if (node.requiresCeilMatch) {
      if (floorMatch) {
        // Both floor and ceil blocks are needed. Stack a fake node to trigger that.
        matchResult.reset(-1, true, true);
        stackNode().follow(node, matchResult);
      } else {
        // The iteration is on the last arc. Follow the ceil arcs directly without reading the ceil arc again.
        followCeilArcs(node, true);
      }
      followed = true;
    } else {
      recordLastSkippedArc(node);
    }
    node.nextArc();
    assert node.isArcIterationOver(); // This exhausted node will be poped from the stack.
    return followed;
  }

  private void recordLastSkippedArc(Node node) {
    if (debug) System.out.println("[" + node.depth + "] record skipped arc " + node.toString(node.arc) + " node.output=" + node.output + " arc.output=" + node.arc.output());
    lastSkippedArc.copyFrom(node.arc);
    lastSkippedArcOutput = node.output;
  }

  private void followFloorOrCeilArcs(Node node) throws IOException {
    assert node.requiresFloorMatch || node.requiresCeilMatch;
    if (node.requiresFloorMatch) {
      followFloorArcs(node, false);
      if (node.requiresCeilMatch) {
        node.requiresFloorMatch = false;
        return;
      }
      node.nextTransition(); // Exhaust this node transitions (may have remaining ceil arc to follow/skip).
      assert node.isTransitionIterationOver();
    } else {
      followCeilArcs(node, false);
      node.exhaustArcIteration(); // Exhaust this node arcs (no remaining arcs to follow/skip).
    }
  }

  private void followFloorArcs(Node node, boolean isAlreadyOnFirstArc) throws IOException {
    assert !isAlreadyOnFirstArc || node.isFirstArc();
    if (debug) System.out.println("[" + node.depth + "] follow floor arcs");
    if (isAlreadyOnFirstArc) {
      scratchArc.copyFrom(node.arc);
    } else {
      fst.readFirstTargetArc(node.followArc, scratchArc, fstReader);
    }
    openPreviousBlock(node, getFloorBlockFP(scratchArc, node.output));
  }

  private void followCeilArcs(Node node, boolean isAlreadyOnLastArc) throws IOException {
    assert !isAlreadyOnLastArc || node.isLastArc();
    if (debug) System.out.println("[" + node.depth + "] follow ceil arcs");
    if (isAlreadyOnLastArc) {
      scratchArc.copyFrom(node.arc);
    } else {
      fst.readLastTargetArc(node.followArc, scratchArc, fstReader);
    }
    long ceilBlockFP = getCeilBlockFP(scratchArc, node.output);
    openBlocks(node, ceilBlockFP, ceilBlockFP);
  }

  private long getFloorBlockFP(FST.Arc<Long> arc, Long output) throws IOException {
    while (true) {
      output = outputs.add(output, arc.output());
      if (arc.label() == FST.END_LABEL) {
        return output;
      }
      fst.readFirstTargetArc(arc, arc, fstReader);
    }
  }

  private long getCeilBlockFP(FST.Arc<Long> arc, Long output) throws IOException {
    while (true) {
      output = outputs.add(output, arc.output());
      if (arc.label() == FST.END_LABEL) {
        return output;
      }
      fst.readLastTargetArc(arc, arc, fstReader);
    }
  }

  private Node stackNode() {
    assert branchDepth < branchNodes.length;
    if (++branchDepth == branchNodes.length) {
      branchNodes = ArrayUtil.growExact(branchNodes, ArrayUtil.oversize(branchDepth + 1, RamUsageEstimator.NUM_BYTES_OBJECT_REF));
    }
    Node node = branchNodes[branchDepth];
    if (node == null) {
      node = branchNodes[branchDepth] = new Node(branchDepth);
    }
    return node;
  }

  private Node popNode() {
    assert branchDepth >= 0;
    return --branchDepth == -1 ? null : getCurrentNode();
  }

  private Node getCurrentNode() {
    return branchNodes[branchDepth];
  }

  private void openAllSubBlocks(Node node) throws IOException {
    assert node.arc.label() != FST.END_LABEL;
    fst.readFirstTargetArc(node.followArc, scratchArc, fstReader);
    if (scratchArc.label() == FST.END_LABEL) {
      fst.readNextArc(scratchArc, fstReader);
    }
    long startBlockFP = getFloorBlockFP(scratchArc, node.output);
    fst.readLastTargetArc(node.followArc, scratchArc, fstReader);
    long endBlockFP = getCeilBlockFP(scratchArc, node.output);
    openBlocks(node, maybePreviousBlockFP(node, startBlockFP), endBlockFP);
  }

  private void openPreviousBlock(Node node, long blockFP) throws IOException {
    assert !scanPreviousBlock;
    long previousBlockFP = maybePreviousBlockFP(node, blockFP);
    if (previousBlockFP != blockFP) {
      assert scanPreviousBlock;
      openBlocks(node, previousBlockFP, previousBlockFP);
    }
  }

  private long maybePreviousBlockFP(Node node, long startBlockFP) throws IOException {
    assert !scanPreviousBlock;
    if (debug) System.out.println("previous block check floorMatch=" + node.requiresFloorMatch + " startFP=" + startBlockFP + " inputFP=" + blockInput.getFilePointer() + " skippedOutput=" + lastSkippedArcOutput);
    if (node.requiresFloorMatch && startBlockFP != blockInput.getFilePointer() && lastSkippedArcOutput != null) {
      long lastSkippedBlockFP = getCeilBlockFP(lastSkippedArc, lastSkippedArcOutput);
      lastSkippedArcOutput = null;
      if (debug) System.out.println("needs previous block previousFP=" + lastSkippedBlockFP + " startFP=" + startBlockFP);
      assert lastSkippedBlockFP < startBlockFP;
      startBlockFP = lastSkippedBlockFP;
      scanPreviousBlock = true;
    }
    return startBlockFP;
  }

  private void openBlocks(Node node, long startBlockFP, long endBlockFP) throws IOException {
    assert startBlockFP <= endBlockFP;
    assert blockFPAlwaysIncreases(startBlockFP);
    if (debug) System.out.println("open blocks startFP=" + startBlockFP + " endFP=" + endBlockFP + " inputFP=" + blockInput.getFilePointer());
    initializeHeader(null, startBlockFP);
    if (blockHeader == null) {
      throw newCorruptIndexException("Illegal absence of block", startBlockFP);
    }
    shouldScanBlock = true;
    this.endBlockFP = endBlockFP;
    assert matchIndex == 0;
    setCommonPrefix(node);
  }

  private boolean blockFPAlwaysIncreases(long startBlockFP) {
    if (!firstBlockOpened) {
      firstBlockOpened = true;
      return true;
    }
    assert startBlockFP >= blockInput.getFilePointer() : "startBlockFP=" + startBlockFP + " inputFP=" + blockInput.getFilePointer();
    return true;
  }

  private void setCommonPrefix(Node node) {
    if (scanPreviousBlock) {
      commonPrefixIndex = 0;
    } else {
      commonPrefixIndex = node.commonPrefixIndex;
      matchStates[commonPrefixIndex] = node.commonPrefixState;
    }
  }

  @Override
  public boolean seekExact(BytesRef text) {
    throw new UnsupportedOperationException();
  }

  @Override
  public void seekExact(long ord) {
    throw new UnsupportedOperationException();
  }

  @Override
  public SeekStatus seekCeil(BytesRef text) {
    throw new UnsupportedOperationException();
  }

  @Override
  public void seekExact(BytesRef term, TermState state) {
    throw new UnsupportedOperationException();
  }

  private enum ArcIteration {FIRST, TAIL, OVER}

  private class Node {

    final int depth;

    final FST.Arc<Long> followArc;
    final FST.Arc<Long> arc;
    final FST.Arc<Long> nextArc;
    ArcIteration arcIteration;
    boolean onlyFloorOrCeil;
    boolean requiresFloorMatch;
    boolean requiresCeilMatch;
    int commonPrefixIndex;
    int commonPrefixState;
    Long output;

    final Transition transition;
    int transitionCount;
    int transitionIndex;

    Node(int depth) {
      assert depth >= 0;
      this.depth = depth;
      followArc = new FST.Arc<>();
      arc = new FST.Arc<>();
      nextArc = new FST.Arc<>();
      transition = new Transition();
    }

    Node asRoot() throws IOException {
      reset(fst.getFirstArc(new FST.Arc<>()), outputs.getNoOutput(), AUTOMATON_INITIAL_STATE, false, false);
      return this;
    }

    Node follow(Node node, MatchResult matchResult) throws IOException {
      assert !node.onlyFloorOrCeil;
      reset(node.arc, node.output, matchResult.exactMatchState, matchResult.floorMatch, matchResult.ceilMatch);
      setCommonPrefix(node);
      if (debug) System.out.println("[" + depth + "] stack node" + (onlyFloorOrCeil ? " onlyFloorOrCeil" : "") + " common prefix index=" + commonPrefixIndex + " state=" + commonPrefixState + " output=" + output);
      return this;
    }

    /**
     * Resets this reusable {@link Node}.
     *
     * @param followArc       The {@link FST.Arc} to follow to move to the next FST node, and initialize the iteration
     *                        on its first {@link FST.Arc}, and initialize on the first transition of the automaton state.
     * @param exactMatchState The automaton state to get the {@link Transition}s from; or -1 if none, in this case only
     *                        the ceil block of the sub-branch will be scanned, all other arcs and blocks will be skipped.
     */
    private void reset(FST.Arc<Long> followArc, Long parentOutput, int exactMatchState, boolean floorMatch, boolean ceilMatch) throws IOException {
      assert exactMatchState != -1 || floorMatch || ceilMatch;
      transitionIndex = 0;
      if (exactMatchState == -1) {
        // Fake node to handle floor and/or ceil match.
        onlyFloorOrCeil = true;
        if (!ceilMatch) {
          // Set the last arc to record it is skipped when this node is poped from the stack.
          fst.readLastTargetArc(followArc, arc, fstReader);
        }
        transitionCount = 1; // Fake transition count to ensure this node is not considered exhausted.
      } else {
        onlyFloorOrCeil = false;
        // Read the first arc. It may be a fake final arc for the node.
        fst.readFirstTargetArc(followArc, arc, fstReader);
        if (!arc.isLast()) {
          nextArc.copyFrom(arc);
          fst.readNextArc(nextArc, fstReader);
        }
        transitionCount = automaton.initTransition(exactMatchState, transition);
        if (transitionCount == 0) {
          // Special state to try with 0 transition because it can accept the final arc FST.END_LABEL or floor match.
          transitionIndex = -1;
        } else {
          automaton.getNextTransition(transition);
        }
      }
      this.followArc.copyFrom(followArc);
      requiresFloorMatch = floorMatch;
      requiresCeilMatch = ceilMatch;
      arcIteration = ArcIteration.FIRST;
      output = outputs.add(parentOutput, followArc.output());
    }

    private void setCommonPrefix(Node node) {
      if (onlyFloorOrCeil || node.isLastArc()) {
        // Simply propagate the existing common prefix.
        commonPrefixIndex = node.commonPrefixIndex;
        commonPrefixState = node.commonPrefixState;
      } else {
        // Set a common prefix based on parent node.
        commonPrefixIndex = node.depth;
        commonPrefixState = node.transition.source;
      }
      assert depth >= commonPrefixIndex;
      assert commonPrefixIndex != 0 || commonPrefixState == 0;
    }

    boolean nextArc() throws IOException {
      assert arcIteration != ArcIteration.OVER;
      if (arc.isLast()) {
        arcIteration = ArcIteration.OVER;
        return false;
      }
      arc.copyFrom(nextArc);
      if (!nextArc.isLast()) {
        fst.readNextArc(nextArc, fstReader);
      }
      arcIteration = ArcIteration.TAIL;
      return true;
    }

    boolean isFirstArc() {
      return arcIteration == ArcIteration.FIRST;
    }

    boolean isLastArc() {
      return arc.isLast();
    }

    boolean isArcIterationOver() {
      return arcIteration == ArcIteration.OVER;
    }

    void jumpToLastArc() throws IOException {
      if (!arc.isLast()) {
        if (nextArc.isLast()) {
          nextArc();
        } else {
          fst.readLastTargetArc(followArc, arc, fstReader);
        }
      }
    }

    /** Exhausts the arc iteration without jumping to the last arc. */
    void exhaustArcIteration() {
      arcIteration = ArcIteration.OVER;
    }

    boolean nextTransition() {
      assert transitionIndex >= 0 && transitionIndex < transitionCount;
      if (++transitionIndex < transitionCount) {
        automaton.getNextTransition(transition);
        return true;
      }
      return false;
    }

    boolean isTransitionIterationOver() {
      assert transitionIndex <= transitionCount;
      return transitionIndex == transitionCount;
    }

    boolean drainNoTransitionState() {
      if (transitionCount == 0) {
        transitionIndex = 0;
        return true;
      }
      return false;
    }

    void setNextArc(boolean isFirstArc) throws IOException {
      assert !onlyFloorOrCeil;
      if (!arc.isLast()) {
        nextArc.copyFrom(arc);
        fst.readNextArc(nextArc, fstReader);
      }
      arcIteration = isFirstArc ? ArcIteration.FIRST : ArcIteration.TAIL;
    }

    int setTransitionForLabel(int label) {
      assert !onlyFloorOrCeil;
      if (transitionCount == 0) {
        return -1;
      }
      int destState = runAutomaton.step(transition.source, label);
      if (destState == -1) {
        transitionIndex = transitionCount;
      } else {
        if (transitionIndex != 0) {
          int transitionCount = automaton.initTransition(transition.source, transition);
          assert transitionCount != 0 && transitionCount == this.transitionCount;
          automaton.getNextTransition(transition);
          transitionIndex = 0;
        }
        while (transition.dest != destState) {
          nextTransition();
        }
      }
      return destState;
    }

    @SuppressWarnings("unused")
    String toString(FST.Arc<Long> arc) {
      return (UTF8_TO_STRING ? Character.toString((char) followArc.label()) : Integer.toString(followArc.label()))
          + "->"
          + (arc.label() == -1 ? "[]" : (UTF8_TO_STRING ? Character.toString((char) arc.label()) : Integer.toString(arc.label())));
    }
  }

  private static class MatchResult {

    int exactMatchState;
    boolean floorMatch;
    boolean ceilMatch;
    boolean wildcardSuffix;

    boolean reset(int exactMatchState, boolean floorMatch, boolean ceilMatch) {
      this.exactMatchState = exactMatchState;
      this.floorMatch = floorMatch;
      this.ceilMatch = ceilMatch;
      assert !wildcardSuffix;
      return exactMatchState != -1 || floorMatch || ceilMatch;
    }

    boolean resetForWildcard(boolean floorMatch) {
      this.floorMatch = floorMatch;
      return wildcardSuffix = true;
    }

    @Override
    public String toString() {
      if (exactMatchState != -1 || floorMatch || ceilMatch) {
        return (exactMatchState == -1 ? "" : "exact ") + (floorMatch ? "floor " : "") + (ceilMatch ? "ceil " : "") + "match";
      } else {
        return "no match";
      }
    }
  }
}