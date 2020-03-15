def LCSubStr2(X: str, Y: str):
    """Find the longest common substring of 2 strings"""
    # Create a table to store lengths of longest common suffixes of substrings.
    # lc_suff[i][j] contains length of longest common suffix of X[0..i-1] and Y[0..j-1].
    m = len(X)
    n = len(Y)
    lc_suff = [[0 for i in range(n + 1)]
               for j in range(m + 1)]

    length = 0

    # Index of the cell which contains the maximum value.
    # Used to build up the longest common substring from right to left.
    row, col = 0, 0

    # Build lc_suff[m+1][n+1] in bottom up fashion.
    for i in range(m + 1):
        for j in range(n + 1):
            if i == 0 or j == 0:
                lc_suff[i][j] = 0
            elif X[i - 1] == Y[j - 1]:
                lc_suff[i][j] = lc_suff[i - 1][j - 1] + 1
                if length < lc_suff[i][j]:
                    length = lc_suff[i][j]
                    row = i
                    col = j
            else:
                lc_suff[i][j] = 0

    if length == 0:
        # No common substring exists
        return ""

    resultStr = ['0'] * length

    # traverse up diagonally form the (row, col) cell until lc_suff[row][col] != 0
    while lc_suff[row][col] != 0:
        length -= 1
        resultStr[length] = X[row - 1]  # or Y[col-1]

        # move diagonally up to previous cell
        row -= 1
        col -= 1

    # required longest common substring
    return ''.join(resultStr)


def LCSubStr(l):
    """Find longest common substring among all strings in a list"""
    if len(l) < 2:
        return ""
    else:
        substrings = []
        substring = ""
        while True:
            l = [s.replace(substring, '', 1) for s in l]
            substring = LCSubStr2(l[0], l[1])
            for s in l[2:]:
                substring = LCSubStr2(substring, s)
                if len(substring) < 1:
                    break
            if len(substring) < 1:
                return substrings
            else:
                substrings.append(substring)
