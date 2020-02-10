# Python3 implementation to print
# the longest common substring

# function to find and print
# the longest common substring of
# X[0..m-1] and Y[0..n-1]
def LCSubStr2(X: str, Y: str):
    '''Find the longest common substring of 2 strings'''
    # Create a table to store lengths of
    # longest common suffixes of substrings.
    # Note that lc_suff[i][j] contains length
    # of longest common suffix of X[0..i-1] and
    # Y[0..j-1]. The first row and first
    # column entries have no logical meaning,
    # they are used only for simplicity of program
    m = len(X)
    n = len(Y)
    lc_suff = [[0 for i in range(n + 1)]
               for j in range(m + 1)]

    # To store length of the
    # longest common substring
    length = 0

    # To store the index of the cell
    # which contains the maximum value.
    # This cell's index helps in building
    # up the longest common substring
    # from right to left.
    row, col = 0, 0

    # Following steps build lc_suff[m+1][n+1]
    # in bottom up fashion.
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

    # if true, then no common substring exists
    if length == 0:
        return ""

    # allocate space for the longest
    # common substring
    resultStr = ['0'] * length

    # traverse up diagonally form the
    # (row, col) cell until lc_suff[row][col] != 0
    while lc_suff[row][col] != 0:
        length -= 1
        resultStr[length] = X[row - 1]  # or Y[col-1]

        # move diagonally up to previous cell
        row -= 1
        col -= 1

    # required longest common substring
    return ''.join(resultStr)


def LCSubStr(l):
    '''Find longest common substring among all strings in a list'''
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
