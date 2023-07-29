import os
import ast
import sys
import copy
import json
import pickle
import random


# theory structure:
# {'rules': {<id>: {'antecedent': <set>, 'consequent': <str>, 'level': <int>, 'dirsubs': {<int>, <int>, ...}}, ...}, 'levels': {<int>: {<int>, <int>, ...}}}

def writeHistogram(histogram, fileName, pad=True):
    if pad:
        kmax = max(list(histogram.keys()))
        for k in range(kmax):
            if k not in histogram:
                histogram[k] = 0
    with open(fileName, 'w') as outfile:
        for k in sorted(list(histogram.keys())):
            _ = outfile.write('%d, %d\n' % (k, histogram[k]))

def printRule(theory, rId):
    return ("%d: " % rId) + ", ".join(sorted(list(theory['rules'][rId]['antecedent']))) + " => " + theory['rules'][rId]['consequent'] + (" | %s" % str(sorted(list(theory['rules'][rId]['dirsubs']))))

def printTheory(theory):
    retq = ''
    for k in theory['levels']:
        retq += '%d\n' % k
        for e in sorted(list(theory['levels'][k])):
            retq += '\t%s\n' % printRule(theory, e)
    return retq

def runInference(theory, premise):
    concMap = {}
    for k, r in theory['rules'].items():
        if 0 == len(r['antecedent'].difference(premise)):
            if r['consequent'] not in concMap:
                concMap[r['consequent']] = set()
            concMap[r['consequent']] = concMap[r['consequent']].union(r['antecedent'])
    msr = None
    conclusion = None
    for k, r in theory['rules'].items():
        if 0 == len(r['antecedent'].difference(premise)):
            ok = True
            for conc, prems in concMap.items():
                if conc == r['consequent']:
                    continue
                if 0 != len(prems.difference(r['antecedent'])):
                    ok = False
                    break
            if ok:
                if (msr is None) or (len(msr[0]) > len(r['antecedent'])):
                    msr = (r['antecedent'], r['consequent'])
                    conclusion = r['consequent']
    return conclusion, msr

def runInference_TeamDefeat(theory, premise):
    def _shadow(theory, rId):
        retq = set()
        todo = set(theory['rules'][rId]['dirsubs'])
        while todo:
            cr = todo.pop()
            if cr in retq:
                continue
            retq.add(cr)
            todo = todo.union(theory['rules'][cr]['dirsubs'])
        return retq
    possibles = set()
    forbiddens = set()
    msr = None
    for k in sorted(theory['levels'].keys()):
        levelIds = theory['levels'][k]
        for j in levelIds:
            if j in forbiddens:
                continue
            if 0 == len(theory['rules'][j]['antecedent'].difference(premise)):
                possibles.add(theory['rules'][j]['consequent'])
                msr = (theory['rules'][j]['antecedent'], theory['rules'][j]['consequent'])
                forbiddens = forbiddens.union(_shadow(theory, j))
    if 1 != len(possibles):
        return None, None
    return list(possibles)[0], msr

def removeRule(theory, premise):
    dk = None
    for k, r in theory.get('rules', {}).items():
        if (0 == len(r['antecedent'].difference(premise))) and (0 == len(premise.difference(r['antecedent']))):
            dk = k
            break
    if dk is None:
        return
    Sb = theory['rules'][dk]['dirsubs']
    level = theory['rules'][dk]['level']
    Sp = set()
    for k, r in theory['rules'].items():
        if dk in r['dirsubs']:
            Sp.add(k)
    for k in Sp:
        theory['rules'][k]['dirsubs'] = theory['rules'][k]['dirsubs'].union(Sb).difference([dk])
    theory['levels'][level].remove(dk)
    theory['rules'].pop(dk)
    # TODO: sanity checks on theories:
    # - no empty levels if only adding
    # - if a rule asserts it is at level, the level agrees
    #for k in theory['levels'].keys():
    #    if dk in theory['levels'][level]:
    #        theory['levels'][level].remove(dk)

def hasAntecedent(theory, premise):
    premise = frozenset(premise)
    for k, r in theory['rules'].items():
        if premise == r['antecedent']:
            return True
    return False

def hasRule(theory, premise, conclusion):
    for k, r in theory['rules'].items():
        if (premise == r['antecedent']) and (conclusion == r['consequent']):
            return True
    return False

def addRule(theory, premise, conclusion):
    def _pushDown(theory, Sb):
        todo = set(Sb)
        done = set()
        while todo:
            cr = todo.pop()
            if cr in done:
                continue
            done.add(cr)
            oldLevel = theory['rules'][cr]['level']
            newLevel = oldLevel + 1
            # TODO: fix this level/rule incosistency
            #theory['levels'][oldLevel].remove(cr)
            for k in theory['levels']:
                if cr in theory['levels'][k]:
                    theory['levels'][k].remove(cr)
            if newLevel not in theory['levels']:
                theory['levels'][newLevel] = set()
            theory['levels'][newLevel].add(cr)
            theory['rules'][cr]['level'] = newLevel
            todo = todo.union(theory['rules'][cr]['dirsubs'])
    if 'levels' not in theory:
        theory['rules'] = {0: {'antecedent': premise, 'consequent': conclusion, 'level': 0, 'dirsubs': set()}}
        theory['levels'] = {0: set([0])}
        return 0
    premise = frozenset(premise)
    removeRule(theory, premise)
    Sp = set()
    Sb = set()
    for e, r in theory['rules'].items():
        if 0 == len(r['antecedent'].difference(premise)):
            Sb.add(e)
        if 0 == len(premise.difference(r['antecedent'])):
            Sp.add(e)
    while True:
        toR = set()
        for e in Sp:
            if 0 < len(theory['rules'][e]['dirsubs'].intersection(Sp)):
                toR.add(e)
        if 0 == len(toR):
            break
        Sp = Sp.difference(toR)
    while True:
        toR = set()
        for e in Sb:
            toR = toR.union(theory['rules'][e]['dirsubs'])
        ki = len(Sb)
        Sb = Sb.difference(toR)
        ko = len(Sb)
        if ki == ko:
            break
    level = 0
    if 0 < len(Sp):
        levels = [theory['rules'][x]['level'] for x in Sp]
        level = max(levels) + 1
    nId = max(list(theory['rules'].keys())) + 1
    theory['rules'][nId] = {'antecedent': premise, 'consequent': conclusion, 'level': level, 'dirsubs': Sb}
    if level not in theory['levels']:
        theory['levels'][level] = set()
    theory['levels'][level].add(nId)
    Sb = [x for x in Sb if level == theory['rules'][x]['level']]
    for e in Sp:
        theory['rules'][e]['dirsubs'] = theory['rules'][e]['dirsubs'].difference(Sb)
        theory['rules'][e]['dirsubs'].add(nId)
    _pushDown(theory, Sb)
    return nId

restrictionBias = {
    '': {'color', 'dimension', 'material', 'physical', 'price', 'shape', 'size', 'transparency', 'weight'},
    'color': {'', 'material', 'physical', 'price', 'transparency'},
    'dimension': {'', 'material', 'physical', 'price', 'shape', 'size', 'weight'},
    'material': {'', 'color', 'dimension', 'physical', 'price', 'shape', 'size', 'transparency', 'weight'},
    'physical': {'', 'color', 'dimension', 'material', 'shape', 'size', 'transparency', 'weight'},
    'price': {'', 'material', 'size', 'weight'},
    'shape': {'', 'dimension', 'material', 'physical', 'size', 'transparency', 'weight'},
    'size': {'', 'dimension', 'material', 'physical', 'shape', 'weight'},
    'transparency': {'', 'color', 'dimension', 'material', 'physical', 'price', 'size'},
    'weight': {'', 'dimension', 'material', 'size'},
    'cleanliness': {'dampness', 'fullness', 'place', 'room', 'temperature', '', 'material', 'physical', 'price', 'transparency'},
    'dampness': {'room', 'place', '', 'cleanliness', 'fullness', 'temperature'},
    'fullness': {'cleanliness', 'dampness', 'place', 'room', 'temperature', '', 'material', 'physical'},
    'place': {'cleanliness', 'dampness', 'fullness', 'room', 'temperature', '', 'dimension', 'material', 'physical', 'price', 'shape', 'size'},
    'room': {'cleanliness', 'dampness', 'fullness', 'place', 'temperature', '', 'dimension', 'material', 'physical', 'price', 'shape', 'size'},
    'temperature': {'room', 'place', 'dampness', 'fullness'},
}

def qualityPrefix(s):
    if '_' in s:
        return s[:s.find('_')]
    return ''

def datasetFromRecords(records):
    dataset = []
    for r in records:
        for k, d in enumerate(r):
            dataset.append((frozenset(r[:k] + r[k+1:]), d))
    return dataset

def splitDataset(pairs, mutexsets):
    retq = {}
    for pair in pairs:
        premise, conclusion = pair
        prefix = qualityPrefix(conclusion)
        if prefix not in retq:
            retq[prefix] = []
        retq[prefix].append(pair)
    return list(retq.values())

def getMutexMap(mutexsets):
    retq = {}
    for ms in mutexsets:
        for e in ms:
            retq[e] = ms.difference([e])
    return retq

def getDatasetAndAuxiliaries():
    records = [ast.literal_eval(x) for x in open("records_dfl.txt").read().splitlines() if x.strip()]
    mutexsetsByKey = {}
    for r in records:
        for e in r:
            k = qualityPrefix(e)
            if k not in mutexsetsByKey:
                mutexsetsByKey[k] = set()
            mutexsetsByKey[k].add(e)
    mutexsets = list(mutexsetsByKey.values())
    dataset = datasetFromRecords(records)
    mutexMap = getMutexMap(mutexsets)
    vocabulary = set(mutexMap.keys())
    return dataset, mutexsets, mutexMap, vocabulary

def getDSMS(dataset, mutexsets, prefix):
    datasets = splitDataset(dataset, mutexsets)
    for k, e in enumerate(mutexsets):
        if prefix == qualityPrefix(list(e)[0]):
            return datasets[k], e
    return None, None

def argMaxUnique(d):
    maxVal = None
    argMax = []
    for k, v in d.items():
        if (None == maxVal) or (maxVal < v):
            argMax = [k]
        elif (maxVal == v):
            argMax.append(k)
    if 1 == len(argMax):
        return argMax[0]
    return None

def prepConflictDataset(pairs, mutexset):
    dataset = {}
    for pair in pairs:
        premise, conclusion = pair
        premise = frozenset(premise)
        if premise not in dataset:
            dataset[premise] = {}
        if conclusion not in dataset[premise]:
            dataset[premise][conclusion] = 0
        dataset[premise][conclusion] = dataset[premise][conclusion] + 1
    retq = []
    for premise in dataset:
        argMax = argMaxUnique(dataset[premise])
        if None != argMax:
           retq.append((premise, argMax))
    return retq

def compatible(premise, term, mutexMap):
    if term not in mutexMap:
        return True
    for t in premise:
        if t in mutexMap[term]:
            return False
    return True

def compatiblePremises(a, b, mutexMap):
    for e in a:
        for f in b:
            if f in mutexMap[e]:
                return False
    return True

def testTheory(theory, dataset, returnCorrects=True):
    correct = 0
    errors = []
    for premise, conclusion in dataset:
        if conclusion == runInference(theory, premise)[0]:
            correct += 1
        else:
            errors.append(premise)
    if not returnCorrects:
        return errors
    return correct

def testAgreement(dataset, theoryA, theoryB):
    disagreements = []
    for premise, _ in dataset:
        cA, msrA = runInference(theoryA, premise)
        cB, msrB = runInference(theoryB, premise)
        if (cA != cB) and (msrA is not None):
            disagreements.append(premise)
    return disagreements

def update(theoryB, d, msrA):
    for k in list(theoryB['rules'].keys()):
        rB = theoryB['rules'][k]
        # Ignore agreeable rules, defeated rules, and inapplicable ones.
        if (msrA[1] == rB['consequent']) or (0 == len(rB['antecedent'].difference(msrA[0]))) or (0 != len(rB['antecedent'].difference(d))):
            continue
        # Remove applicable rules that would disagree with the new one
        removeRule(theoryB, rB['antecedent'])
    addRule(theoryB, msrA[0], msrA[1])

def instructStep(theoryA, theoryB, dataset, disagreements, mutexMap):
    if 0 == len(disagreements):
        return [], None
    random.shuffle(disagreements)
    d = disagreements[0]
    _, msrA = runInference(theoryA, d)
    update(theoryB, d, msrA)
    return testAgreement(dataset, theoryA, theoryB), d

if "__main__" == __name__:
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
    dataset, mutexsets, mutexMap, vocabulary = getDatasetAndAuxiliaries()
    datasetTemperature, mutexsetTemperature = getDSMS(dataset, mutexsets, prefix)
    samples = 100
    entries = []
    theoryFiles = [os.path.join('./theories_specprio/', f) for f in os.listdir('./theories_specprio') if os.path.isfile(os.path.join('./theories_specprio/', f))]
    for f in theoryFiles:
        theory = pickle.load(open(f, 'rb'))
        entries.append(theory)
    histogramStepcount = {0:0}
    histogramBackslides = {0:0}
    histogramForgottenInstructions = {0:0}
    entryIndices = list(range(len(entries)))
    for k in range(samples):
        random.shuffle(entryIndices)
        random.shuffle(datasetTemperature)
        theoryA = copy.deepcopy(entries[entryIndices[0]])
        theoryB = copy.deepcopy(entries[entryIndices[1]])
        cdata = datasetTemperature[int(0.7*len(datasetTemperature)):]
        disagreements = testAgreement(cdata, theoryA, theoryB)
        instructions = []
        stepcount = 0
        maxbackslides = 0
        previousDisagreementCount = len(disagreements)
        forgotten = 0
        with open('specprio_disagreementcounts.csv', 'w') as outfile:
            _ = outfile.write('%d, %d\n' % (stepcount, len(disagreements)))
            while (0 < len(disagreements)) and (stepcount < 200): # Just in case theories never come into agreement
                stepcount += 1
                disagreements, d = instructStep(theoryA, theoryB, cdata, disagreements, mutexMap)
                _ = outfile.write('%d, %d\n' % (stepcount, len(disagreements)))
                if 0 < forgotten:
                    sys.exit()
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
    writeHistogram(histogramStepcount, 'specprio_stepcount.csv')
    writeHistogram(histogramBackslides, 'specprio_backslides.csv')
    writeHistogram(histogramForgottenInstructions, 'specprio_forgotten.csv', False)

