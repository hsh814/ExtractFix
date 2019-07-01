#!/usr/bin/env python3

factor = 10

def levenshtein_distance(s, t):
    # for all i and j, d[i,j] will hold the Levenshtein distance between
    # the first i characters of s and the first j characters of t
    # note that d has (m+1)*(n+1) values
    n = len(t)
    m = len(s)
    d = [[0 for i in range(n+1)] for j in range(m+1)]
 
    # source prefixes can be transformed into empty string by
    # dropping all characters
    for i in range(m+1):
        d[i][0] = i*factor
 
    # target prefixes can be reached from empty source prefix
    # by inserting every character
    for j in range(n+1):
        d[0][j] = j*factor
 
    for j in range(1, n+1):
        for i in range(1, m+1):
            if s[i-1] == t[j-1]:
                cost = 0
            elif s[i-1].isdigit() and t[j-1].isdigit():
                cost = abs(int(s[i-1]) - int(t[j-1]))
            else:
                cost = factor
            d[i][j] = min(d[i-1][j] + factor, d[i][j-1] + factor, d[i-1][j-1] + cost)
            # print(str(i), str(j), str(d[i][j]))

    return d[m][n]


dis = levenshtein_distance(["(", "-", "varA", "varC", ")"], ["varC"])
# print(dis)
