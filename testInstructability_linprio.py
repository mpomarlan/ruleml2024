import os
import copy
import pickle
import testing
import random

def writeHistogram(histogram, fileName, binsize=1):
    histogramAdj = {}
    for k, v in histogram.items():
        bink = (k//binsize)
        bink = bink*binsize + binsize
        if bink not in histogramAdj:
            histogramAdj[bink] = 0
        histogramAdj[bink] += v
    with open(fileName, 'w') as outfile:
        for k in sorted(list(histogramAdj.keys())):
            _ = outfile.write('%d, %d\n' % (k, histogramAdj[k]))

def loadTheoriesAndRecords(fileName):
    with open(fileName, 'rb') as infile:
       data = pickle.load(infile)
    pref2Theory = testing.makePref2TheoryMap(data['theory'])
    trainRecords = data['records'][:int(len(data['records'])*0.7)]
    testRecords = data['records'][int(len(data['records'])*0.7):]
    return pref2Theory, trainRecords, testRecords
    
def testTheory(pref2Theory, testRecords, prefix):
    failedRecords = []
    for r in testRecords:
        conc, prem = testing.makeTestcase(r, prefix)
        msr, osr = testing.getAndExplainConclusion(prem, pref2Theory[prefix])
        if (msr is None) or (conc != msr[1]):
            failedRecords.append(r)
    return failedRecords
    
def testAgreement(pref2TheoryA, pref2TheoryB, testRecords, prefix):
    disagreements = []
    for r in testRecords:
        _, prem = testing.makeTestcase(r, prefix)
        msrA, _ = testing.getAndExplainConclusion(prem, pref2TheoryA[prefix])
        msrB, _ = testing.getAndExplainConclusion(prem, pref2TheoryB[prefix])
        if (msrA is None):
            continue
        if (msrB is None) or (msrA[1] != msrB[1]):
            disagreements.append(r)
    return disagreements
    
def instructStep(pref2TheoryA, pref2TheoryB, testRecords, disagreements, prefix):
    random.shuffle(disagreements)
    _, prem = testing.makeTestcase(disagreements[0], prefix)
    msrA, _ = testing.getAndExplainConclusion(prem, pref2TheoryA[prefix])
    msrB, _ = testing.getAndExplainConclusion(prem, pref2TheoryB[prefix])
    if msrB is None:
        pref2TheoryB[prefix].append(msrA)
    else:
        #print("Update (%s) ::: (%s)" % (testing.printRule(msrB), testing.printRule(msrA)))
        testing.updateTheory(msrB, pref2TheoryB[prefix], msrA)
    return testAgreement(pref2TheoryA, pref2TheoryB, testRecords, prefix), disagreements[0]

def runTesting():
    def _getForgottenCount(disagreements, instructions):
        retq = 0
        toRemove = []
        for e in instructions:
            if e in disagreements:
                retq += 1
                toRemove.append(e)
        for e in toRemove:
            instructions.remove(e)
        return retq
    prefix = 'temperature'
    samples = 100
    entries = []
    theoryFiles = [os.path.join('./theories_linprio/', f) for f in os.listdir('./theories_linprio') if os.path.isfile(os.path.join('./theories_linprio/', f))]
    for f in theoryFiles:
        pref2Theories, training, testing = loadTheoriesAndRecords(f)
        entries.append((pref2Theories, training, testing))
    histogramStepcount = {0:0}
    histogramBackslides = {0:0}
    histogramForgottenInstructions = {0:0}
    entryIndices = list(range(len(entries)))
    for k in range(samples):
        random.shuffle(entryIndices)
        theoriesA, trainA, _ = copy.deepcopy(entries[entryIndices[0]])
        theoriesB, _, _ = copy.deepcopy(entries[entryIndices[1]])
        disagreements = testAgreement(theoriesA, theoriesB, trainA, prefix)
        instructions = []
        stepcount = 0
        maxbackslides = 0
        previousDisagreementCount = len(disagreements)
        forgotten = 0
        with open('linprio_disagreementcounts.csv', 'w') as outfile:
            _ = outfile.write('%d, %d\n' % (stepcount, len(disagreements)))
            while (0 < len(disagreements)) and (stepcount < 200): # Just in case theories never come into agreement
                stepcount += 1
                disagreements, d = instructStep(theoriesA, theoriesB, trainA, disagreements, prefix)
                _ = outfile.write('%d, %d\n' % (stepcount, len(disagreements)))
                forgotten += _getForgottenCount(disagreements, instructions)
                instructions.append(d)
                backslides = len(disagreements) - previousDisagreementCount
                if maxbackslides < backslides:
                    maxbackslides = backslides
                previousDisagreementCount = len(disagreements)
            if stepcount not in histogramStepcount:
                histogramStepcount[stepcount] = 0
            histogramStepcount[stepcount] += 1
            if maxbackslides not in histogramBackslides:
                histogramBackslides[maxbackslides] = 0
            histogramBackslides[maxbackslides] += 1
            if forgotten not in histogramForgottenInstructions:
                histogramForgottenInstructions[forgotten] = 0
            histogramForgottenInstructions[forgotten] += 1
        if 190 < stepcount:
           print("Particularly bad string of updates: %d steps for teacher %d student %d" % (stepcount, entryIndices[0], entryIndices[1]))
    writeHistogram(histogramStepcount, 'linprio_stepcount.csv', binsize=10)
    writeHistogram(histogramBackslides, 'linprio_backslides.csv', binsize=20)
    writeHistogram(histogramForgottenInstructions, 'linprio_forgotten.csv', binsize=20)

if "__main__" == __name__:
    runTesting()

