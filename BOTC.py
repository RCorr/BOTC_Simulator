# python -m venv venv
# venv/scripts/activate
# pip install numpy
# pip install scipy
# python BOTC.py

import random
import math
import numpy as np
from scipy import stats
from itertools import combinations
from itertools import permutations
from itertools import product
from collections import Counter
import time
# from multiprocessing import Process, Manager
import concurrent.futures
from multiprocessing import Array
from multiprocessing.sharedctypes import RawArray
from enum import Enum, IntEnum, unique
import copy
import sys
from functools import partial, wraps
import os
import queue

@unique
class Role(IntEnum): # IntEnum slows down a lot; from 16 to 74 sec
    WASHERWOMAN = 1 # minion supports demon as town
    LIBRARIAN = 2 # minion supports demon as outsider, minion accuses others as drunk
    INVESTIGATOR = 3 # minion accuses others as minion
    CHEF = 4 # minion say opposite
    EMPATH = 5 # demon say opposite
    FORTUNE_TELLER = 6
    UNDERTAKER = 7
    MONK = 8 # demon claim
    RAVENKEEPER = 9 # demon claim
    VIRGIN = 10
    SLAYER = 11
    SOLDIER = 12 # demon claim
    MAYOR = 13
    BUTLER = 14
    SAINT = 15 # demon claim
    RECLUSE = 16
    DRUNK = 17
    POISONER = 18
    SPY = 19
    BARON = 20
    SCARLET_WOMAN = 21
    IMP = 22 # ^ Can convert to lower()

@unique
class Info(Enum):
    MYSELF = 1
    CLAIM = 2
    ABILITY = 3
    DEATH = 4

@unique
class AbilityAct(Enum):
    CORRECT = 1
    DROISON = 2
    LYING = 3

@unique
class PrivateChat(Enum):
    WASH = 1
    LIBR = 2
    EVIL = 3

class Script:
    def __init__(self, poss_town_roles, poss_out_roles, poss_minion_roles, poss_demon_roles, role_dict, distributions, all_permutations=None):
        self.poss_town_roles = poss_town_roles
        self.poss_out_roles = poss_out_roles
        self.poss_minion_roles = poss_minion_roles
        self.poss_demon_roles = poss_demon_roles
        self.role_dict = role_dict
        self.distributions = distributions
        # self.all_permutations = all_permutations

def timethis(f):
    @wraps(f)
    def wrap(*args, **kw):
        ts = time.time()
        result = f(*args, **kw)
        te = time.time()
        td = te - ts
        if td > 0:
            print('func:%r args:[%r, %r] took: %2.6f sec' % (f.__name__, len(args), len(kw), td), flush=True, file=sys.stderr)
        return result
    return wrap

# Helper functions for running roles
def randint_exclude(start, end, exclude):
    return random.choice([i for i in range(start, end) if i not in exclude])

def rand_role(list, exclude):
    if exclude in list:
        list.remove(exclude)
    return random.choice(list)

def get_alive_neighbor(town, position, direction):
    neighbor = (position+direction)%town.size
    if town.players[neighbor].alive:
        return neighbor
    return get_alive_neighbor(town, neighbor, direction)


# Functions for running roles
# Info is: Role, Date, Position, Truth
def give_washerwoman_info(town, position, truth):
    if town.date > 1: return None
    output = []; holder = town.players.copy(); random.shuffle(holder); first = True; second = True
    match truth:
        case AbilityAct.CORRECT:
            for player in holder:
                if player.player_number != position:
                    if player.type == 't' and first:
                        output = [Role(player.role)] + output + [player.player_number]; first = False
                    elif second:
                        output = output + [player.player_number]; second = False
        case AbilityAct.DROISON:
            first = randint_exclude(0, town.size, [position])
            return [rand_role(poss_town_roles, Role.WASHERWOMAN), first, randint_exclude(0, town.size, [position, first])]
        case AbilityAct.LYING:
            demon_pos = check_for_alive_demon(town) # TODO: Fix claim
            return [town.players[demon_pos].claim, demon_pos, randint_exclude(0, town.size, [position, demon_pos])]
    # TODO: make not ancidentally correct. make better at lying --> need to be correct. can see self
    return output

def check_washerwoman_info(permutation, info):
    townie = info
    output = (True if permutation[townie[1]] == townie[0] or permutation[townie[2]] == townie[0] else False)
    return output

def give_librarian_info(town, position, truth):
    if town.date > 1: return None
    output = []; holder = town.players.copy(); random.shuffle(holder); first = True; second = True
    match truth:
        case AbilityAct.CORRECT:
            for player in holder:
                if player.player_number != position:
                    if player.type == 'o' and first:
                        output = [Role(player.role)] + output + [player.player_number]; first = False
                    elif second:
                        output = output + [player.player_number]; second = False
            if first: output = 0
        case AbilityAct.DROISON:
            first = randint_exclude(0, town.size, [position])
            return [random.choice(poss_out_roles), first, randint_exclude(0, town.size, [position, first])]
        case AbilityAct.LYING:
            demon_pos = check_for_alive_demon(town) # TODO: Fix claim
            return [town.players[demon_pos].claim, demon_pos, randint_exclude(0, town.size, [position, demon_pos])]
    
    # TODO: make not ancidentally correct. Also make 0 possible. If no baron, evil should say 0? Don't show an in-game role?
    return output

def check_librarian_info(permutation, info):
    outie = info
    if outie == 0:
        for role in permutation:
            if get_role_type(role) == 'o':
                return False
        return True
    output = (True if permutation[outie[1]] == outie[0] or permutation[outie[2]] == outie[0] else False)
    return output

def give_investigator_info(town, position, truth):
    if town.date > 1: return None
    output = []; holder = town.players.copy(); random.shuffle(holder); first = True; second = True
    match truth:
        case AbilityAct.CORRECT:
                for player in holder:
                    if player.player_number != position:
                        if player.type == 'm' and first:
                            output = [Role(player.role)] + output + [player.player_number]; first = False
                        elif second:
                            output = output + [player.player_number]; second = False
        case AbilityAct.DROISON:
            first = randint_exclude(0, town.size, [position])
            return [random.choice(poss_minion_roles), first, randint_exclude(0, town.size, [position, first])]
        case AbilityAct.LYING:
            first = randint_exclude(0, town.size, [position])
            return [random.choice(poss_minion_roles), first, randint_exclude(0, town.size, [position, first])]
    # TODO: make not ancidentally correct
    return output

def check_investigator_info(permutation, info):
    minion = info
    output = (True if permutation[minion[1]] == minion[0] or permutation[minion[2]] == minion[0] else False)
    return output

def give_chef_info(town, position, truth):
    if town.date > 1: return None
    output = 0
    for i in range(town.size):
        if town.players[i].alignment == 'Evil':
            output += (1 if town.players[i-1].alignment == 'Evil' else 0)
    match truth:
        case AbilityAct.CORRECT:
            return output
        case AbilityAct.DROISON | AbilityAct.LYING:
            return (0 if output >= 1 else 1)
        #case AbilityAct.LYING:
    return output

def check_chef_info(permutation, info):
    number = info; check = 0
    for i in range(len(permutation)):
        if get_role_alignment(permutation[i]) == 'Evil':
            check += (1 if get_role_alignment(permutation[i-1]) == 'Evil' else 0)
    if check == number:
        return True
    return False

def give_empath_info(town, position, truth):
    left = get_alive_neighbor(town, position, -1)
    right = get_alive_neighbor(town, position, 1)
    output = [(1 if town.players[left].alignment == 'Evil' else 0) + \
              (1 if town.players[right].alignment == 'Evil' else 0)] + [left] + [right]
    match truth:
        case AbilityAct.CORRECT:
            return output
        case AbilityAct.DROISON | AbilityAct.LYING:
            output[0] = (0 if output[0] >= 1 else 1)
        # case AbilityAct.LYING:
    
    #and bool(random.randint(0,1))
    return output

def check_empath_info(permutation, info):
    numbers = info
    check = (1 if get_role_alignment(permutation[numbers[1]]) == 'Evil' else 0) + \
    (1 if get_role_alignment(permutation[numbers[2]]) == 'Evil' else 0)
    if check == numbers[0]:
        return True
    return False

def give_fortune_teller_info(town, position, truth):
    return None
    match truth:
        case AbilityAct.CORRECT:
            pass
        case AbilityAct.DROISON:
            pass
        case AbilityAct.LYING:
            pass
    output = False
    if get_role_type(town[choice[0]].role) == 'd' or get_role_type(town[choice[1]].role) == 'd':
        output = True
    return [output, choice[0], choice[1]]

def check_fortune_teller_info(permutation, info):
    pass

def give_undertaker_info(town, position, truth):
    if town.date == 1: return None
    match truth:
        case AbilityAct.CORRECT:
            if town.previous_day_execution != None:
                return [town.previous_day_execution[0], town.previous_day_execution[1]]
        case AbilityAct.DROISON | AbilityAct.LYING:
            if town.previous_day_execution != None:
                return [town.previous_day_execution[0], \
                    rand_role(poss_town_roles+poss_out_roles+poss_minion_roles+poss_demon_roles, Role.UNDERTAKER)] # Own role could be seen with spy, bad lying
        # case AbilityAct.LYING:
    # Maybe not the right way to do this
    
    return None

def check_undertaker_info(permutation, info):
    executed = info
    return permutation[executed[0]] == executed[1]

def monk_protection(town, position, truth):
    if town.date == 1: return None
    choose_random_player(town, 0, True, town.players[position]).single_night_conditions.append('no_demon')
    return None

def give_ravenkeeper_info(town, position, truth):
    player = town.players[position]
    if player.just_died and player.death_source != 'execute':
        player.just_died = False
        match truth:
            case AbilityAct.CORRECT:
                max = [0, 0.0]
                for i in range(town.size):
                    if town.players[i].alive and player.wv.evil_analysis[i] > max[1]: # Change selection code
                        max = [i, player.wv.evil_analysis[i]]
                return [max[0], town.players[max[0]].role]
            case AbilityAct.DROISON | AbilityAct.LYING:
                return [0, rand_role(poss_town_roles+poss_out_roles+poss_minion_roles+poss_demon_roles, Role.RAVENKEEPER)] # TODO: Change first value
    return None

def check_ravenkeeper_info(permutation, info): # [0, 'Role']
    if permutation[info[0]] == info[1]:
        return True
    return False

def soldier_protection(town, position, truth):
    town.players[position].single_night_conditions.append('no_demon')
    return None

def imp_kill(town, position, truth):
    if town.date == 1: return None
    analysis = town.players[position].wv.analysis
    options = np.dot(analysis, demon_kill_preference) # can use @
    # print(options)
    max = [-1000000, 0] # Bad way to intialize
    for i in range(town.size):
        if town.players[i].alive and options[i] > max[0]:
            max = [options[i], i] # TODO: Should also be based on suspicion
    # print(max)
    kill_player(town, town.players[max[1]], 'demon')
    return None


def find_all_permutations(dist):
    # combinations(iterable, r)
    # Baron is still kinda jank
    less_minions = poss_minion_roles.copy(); less_minions.remove(Role.BARON)
    t = list(combinations(poss_town_roles, int(dist[0])))
    o = list(combinations(poss_out_roles, int(dist[1])))
    m = list(combinations(less_minions, int(dist[2])))
    d = list(combinations(poss_demon_roles, int(dist[3])))
    output = turn_combs_to_perms(t, o, m, d, int(np.sum(dist)))
    
    #might need to clamp
    bt = list(combinations(poss_town_roles, int(dist[0]-2))); bo = list(combinations(poss_out_roles, int(dist[1]+2)))
    exclude_baron_set = (list(combinations(less_minions, int(dist[2]-1))))
    bm = []
    for each in exclude_baron_set:
        bm.append(each + (Role.BARON,))
    out2 = turn_combs_to_perms(bt, bo, bm, d, int(np.sum(dist)))
    output = np.concatenate((output, out2), axis=0)

    for i in range(len(output)):
        output[i] = np.array(output[i])

    # print(type(output))
    # print(type(output[0]))
    # print(output[0])
    # print(output[300000])
    # print(output[-1])
    # print(len(output))

    return output

def turn_combs_to_perms(l1, l2, l3, l4, size):
    output = []
    comb = (list(product(l1, l2, l3, l4)))
    for c in comb:
        combination = c[0] + c[1] + c[2] + c[3]
        output.extend(permutations(combination, size))
    return np.array(output)

# Script and creating permutations

# if __name__ == '__main__':
poss_town_roles = [Role.WASHERWOMAN, Role.LIBRARIAN, Role.INVESTIGATOR, Role.CHEF, Role.EMPATH, \
                    Role.UNDERTAKER, Role.MONK, Role.SOLDIER]
poss_out_roles = [Role.SAINT, Role.DRUNK]
poss_minion_roles = [Role.SCARLET_WOMAN, Role.BARON]

# poss_town_roles = [Role.WASHERWOMAN, Role.LIBRARIAN, Role.INVESTIGATOR, Role.CHEF, Role.EMPATH, Role.FORTUNE_TELLER, \
#                   Role.UNDERTAKER, Role.MONK, Role.RAVENKEEPER, Role.VIRGIN, Role.SLAYER, Role.SOLDIER, Role.MAYOR]
# poss_out_roles = [Role.SAINT, Role.DRUNK, Role.RECLUSE, Role.BUTLER]
# poss_minion_roles = [Role.SCARLET_WOMAN, Role.POISONER, Role.SPY, Role.BARON]

poss_demon_roles = [Role.IMP]
first_night_order = [Role.POISONER, Role.SPY, Role.WASHERWOMAN, Role.LIBRARIAN, Role.INVESTIGATOR, Role.CHEF, Role.EMPATH, \
                    Role.FORTUNE_TELLER, Role.BUTLER] # Change to use role dict
later_night_order = [Role.POISONER, Role.SOLDIER, Role.MONK, Role.SPY, Role.IMP, Role.RAVENKEEPER, Role.UNDERTAKER, Role.EMPATH, Role.FORTUNE_TELLER, Role.BUTLER]

demon_kill_preference = np.array([0, 0, 0, 0, 0, 1, 2, 2, 3, -3, 2, 2, -3, -3, -1, -1, -1, -1, -2, -2, -2, -2, -4]) # Indexed at 1, compare to Role(IntEnum)
good_execute_preference = np.array([0, 0, 0, 0, 0, -1, -2, -2, -2, -2, -2, -2, -2, -3, 1, -3, 1, 1, 2, 2, 2, 2, 3]) # Really not sure about these numbers

WASHERWOMAN = 0
LIBRARIAN = 0
INVESTIGATOR = 0
CHEF = 0
EMPATH = -1
FORTUNE_TELLER = -2
UNDERTAKER = -2
MONK = -2
RAVENKEEPER = -2
VIRGIN = -2
SLAYER = -2
SOLDIER = -2
MAYOR = -3
BUTLER = 1
SAINT = -3
RECLUSE = 1
DRUNK = 1
POISONER = 2
SPY = 2
BARON = 2
SCARLET_WOMAN = 2
IMP = 3 # ^ Can convert to lower()

role_dict = { #Name : 
    Role.WASHERWOMAN: ['t', give_washerwoman_info, check_washerwoman_info],
    Role.LIBRARIAN: ['t', give_librarian_info, check_librarian_info],
    Role.INVESTIGATOR: ['t', give_investigator_info, check_investigator_info],
    Role.CHEF: ['t', give_chef_info, check_chef_info],
    Role.EMPATH: ['t', give_empath_info, check_empath_info],
    Role.FORTUNE_TELLER: ['t', give_fortune_teller_info, check_fortune_teller_info],
    Role.UNDERTAKER: ['t', give_undertaker_info, check_undertaker_info],
    Role.MONK: ['t', monk_protection, None],
    Role.RAVENKEEPER: ['t', give_ravenkeeper_info, check_ravenkeeper_info],
    Role.VIRGIN: ['t', None, None],
    Role.SLAYER: ['t', None, None],
    Role.SOLDIER: ['t', soldier_protection, None],
    Role.MAYOR: ['t', None, None],

    Role.BUTLER: ['o', None, None],
    Role.SAINT: ['o', None, None],
    Role.DRUNK: ['o', None, None],
    Role.RECLUSE: ['o', None, None],
    
    Role.SCARLET_WOMAN: ['m', None, None],
    Role.POISONER: ['m', None, None],
    Role.SPY: ['m', None, None],
    Role.BARON: ['m', None, None],
    
    Role.IMP: ['d', imp_kill, None]
}

distributions = {
    7 : np.array([5,0,1,1]),
    8 : np.array([5,1,1,1]),
    9 : np.array([5,2,1,1]),
    10 : np.array([7,0,2,1]),
    11 : np.array([7,1,2,1]),
    12 : np.array([7,2,2,1]),
    13 : np.array([9,0,3,1]),
    14 : np.array([9,1,3,1]),
    15 : np.array([9,2,3,1])
}

# Helper functions for running roles
def get_role_type(role):
    if 0 < Role(role) <= 13:
        return 't'
    if 13 < Role(role) <= 17:
        return 'o'
    if 17 < Role(role) <= 21:
        return 'm'
    if 21 < Role(role) <= 22:
        return 'd'
    return None

def get_role_alignment(role):
    if Role(role) <= 17:
        return 'Good'
    return 'Evil'

def check_for_role(town, role, alive=True):
    # Only finds first role
    out_player = None
    for player in town.players:
        if Role(player.role) == Role(role):
            if (player.alive if alive else True):
                out_player = player
    return out_player

def check_for_alive_demon(town): # Returns int or None
    output = None
    for player in town.players:
        if player.alive and player.type == 'd':
            output = player.player_number
    return output

def role_in_perm(town, perm, role, alive):
    for i in range(town.size):
        if Role(perm[i]) == Role(role):
            if (town.players[i].alive if alive else True):
                return i
    return None

def alive_minion_in_perm(town, perm): # Returns [Bool, player_num]. TODO: Not valid if multiple players of same type
    latest = [-1, 0]
    for i in range(town.size):
        if get_role_type(perm[i]) == 'm':
            if town.players[i].alive:
                return [True, i]
            elif town.players[i].death_order_num > latest[0]:
                latest = [town.players[i].death_order_num, i]
    return [False, latest[1]]

def alive_demon_in_perm(town, perm): # Returns [Bool, player_num]. TODO: Currently, there can't be more than one demon
    latest = [-1, 0]
    for i in range(town.size):
        if get_role_type(perm[i]) == 'd':
            if town.players[i].alive:
                return [True, i]
            elif town.players[i].death_order_num > latest[0]:
                latest = [town.players[i].death_order_num, i]
    return [False, latest[1]]

def evil_type(type):
    if type == 'm' or type == 'd':
       return True
    return False

# Helper functions for running town
def choose_random_player(town, alignment=0, is_alive=True, not_player=None):
    holder = town.players.copy()
    random.shuffle(holder)

    output = None
    for player in holder:
        if player.alive == is_alive and player != not_player and \
        (player.alignment == 'Good' if alignment==1 else True) and (player.alignment == 'Evil' if alignment==-1 else True):
            output = player
            break
    return output

def print_town(town):
    for player in town.players:
        bool_print(player.current())
    bool_print('')

def check_end(town):
    if total_alive(town) < 3 or check_for_alive_demon(town) == None:
        give_win(town, 'Good' if check_for_alive_demon(town) == None else 'Evil')

def give_win(town, team):
    if team == 'Good':
        town.victory = 1
    town.end = True

def total_alive(town):
    life = 0
    for player in town.players:
        if player.alive:
            life += 1
    return life

# 4 player day behavior, remove with extra kills / deaths / toymaker


def start(town, all_permutations):
    assign_town(town, all_permutations)
    perform_night(town)

def assign_town(town, all_permutations):
    roles = random.choice(all_permutations)
    while (Role.SOLDIER in roles) or (Role.WASHERWOMAN in roles) or (Role.SCARLET_WOMAN in roles):
        roles = random.choice(all_permutations)

    # Use intersection to create, will be faster
    town.drunk = poss_town_roles.copy()
    town.bluffs = poss_town_roles.copy() + poss_out_roles.copy()
    town.out_of_play_roles = poss_town_roles.copy() + poss_out_roles.copy() + poss_minion_roles.copy() + poss_demon_roles.copy()
    # TODO: When to bluff outsiders?
    for role in roles:
        if role in town.drunk:
            town.drunk.remove(role)
        if role in town.bluffs:
            town.bluffs.remove(role)
        if role in town.out_of_play_roles:
            town.out_of_play_roles.remove(role)
    random.shuffle(town.drunk)
    town.drunk = town.drunk[0]
    
    if town.drunk in town.bluffs: town.bluffs.remove(town.drunk)
    if Role.DRUNK in town.bluffs: town.bluffs.remove(Role.DRUNK)
    random.shuffle(town.bluffs)
    if len(town.bluffs) >= 3: town.bluffs = town.bluffs[:3]
    
    for i in range(len(roles)):
        role = roles[i]
        new_player = Player(town, role, get_role_type(role), get_role_alignment(role), i)
        town.players.append(new_player)
    
    for player in town.players:
        if player.type == 'd':
            player.claim = Role.SOLDIER
        elif player.type == 'm':
            player.claim = Role.WASHERWOMAN
        #print(Role(player.claim).name)

def perform_day(town):
    if town.date == 1:
        perform_first_info(town)
    else:
        perform_later_info(town)
    # 4 player day behavior, remove with extra kills / deaths / toymaker
    if town.previous_day_execution != None and total_alive(town) == 4:
        town.previous_day_execution = None
    else:
        # nominate a good and an evil player, good players have 1/2 chance to vote for either, evil always and only votes for good, dead votes in final 3
        # if (chopping_block := nominations(town)) != None:
        #     kill_player(chopping_block, 'execute')
        #     town.previous_day_execution = [chopping_block.player_number, chopping_block.role]
        # if total_alive(town) <= 4:
        #     worldview_solver(town, selected_player.wv, True)

        # for player in town:
        #     player.wv = these_futures[player.player_number].result()
            #string_outputs = [future.result() for future in these_futures]
        if total_alive(town) <= 4:
            town.final_day = True
        
        for player in town.players:
            worldview_solver(town, player.wv, town.final_day)

        suspects = []
        for player in town.players:
            if player.alignment == 'Good':
                options = (np.dot(player.wv.analysis, good_execute_preference) if not town.final_day else player.wv.evil_analysis) # TODO: Change to make gradual
                # print(options)s
                max = [-1000000, 0]
                for i in range(town.size):
                    if town.players[i].alive and options[i] > max[0]: # player.wv.world.alive[i]
                        max = [options[i], i]
                    elif town.players[i].alive and options[i] == max[0]: # TODO: Make willing to kill if "close" rather than exactly equal
                        max.append(i)
                suspects.extend(max[1:])
            if player.alignment == 'Evil':
                for i in range(town.size):
                    if town.players[i].alive and player.wv.evil_analysis[i] < 0.1: # TODO: Change magic number
                        suspects.append(i)
        bool_print(suspects)
        chopped = stats.mode(suspects)[0]
        kill_player(town, town.players[chopped], 'execute')
        town.previous_day_execution = [chopped, town.players[chopped].role]
    
    bool_print('\033[1m Day '+ str(town.date) + ' \033[0m')
    town.date = town.date + 1
    print_town(town)
    check_end(town)

def nominations(town):
    player_g = choose_random_player(town, 1)
    votes_g = nomination(town, player_g)

    player_e = choose_random_player(town, -1)
    votes_e = nomination(town, player_e)

    bool_print((votes_g, votes_e))
    # make ties not a thing
    if votes_g > votes_e and votes_g >= math.ceil(total_alive(town)/2.0):
        return player_g
    elif votes_e > votes_g and votes_e >= math.ceil(total_alive(town)/2.0):
        return player_e
    return None

def nomination(town, target):
    votes = 0
    for player in town.players:
        # technically order for dead votes could matter, but it doesn't in a real game
        if player.alive or total_alive(town) <= 4:
            if player.alignment == 'Evil':
                votes += (1 if target.alignment == 'Good' else 0)
            #else if random.random() < 0.5:
                #votes += 1
            else:
                votes += random.randint(0,1)
    return votes


def perform_night(town):
    if town.date == 1:
        for player in town.players:
            if evil_type(player.type):
                for player2 in town.players:
                    if evil_type(player2.type):
                        player.want_chat.put([player2, None, PrivateChat.EVIL])

    for role in (first_night_order if town.date == 1 else later_night_order): # Iterate through the town and check if claim/role and alive
        if role_dict[role][1] != None:
            for player in town.players:
                if player.claim == role or player.role == role:
                    if player.alive or role == Role.RAVENKEEPER:
                        truth = AbilityAct.CORRECT
                        if player.claim != player.role:
                            truth = AbilityAct.DROISON
                        if player.alignment == 'Evil': # TODO: Doesn't cover evil townsfolk or outsiders. Should have 'knows evil' flag. Should trigger during day
                            truth = AbilityAct.LYING
                        info = role_dict[role][1](town, player.player_number, truth)
                        if info != None:
                            player.info.append([Info.ABILITY, Role(role), town.date, player.player_number, info])
                            bool_print(player.info)

        # if (player := check_for_role(town, role, (role != Role.RAVENKEEPER))) != None:
        #     if role_dict[player.claim][1] != None: # What if they claim one thing and have another?
        #         info = role_dict[player.claim][1](town, player.player_number, player.claim == player.role)
        #         if info != None:
        #             player.info.append([Info.ABILITY, Role(player.claim), town.date, player.player_number, info])
        #             bool_print(player.info)
                # if player.role >= 18 and role_dict[player.role][1] != None:
                #     info = role_dict[player.role][1](town, player.player_number, True)
                #     if info != None:
                #         player.info.append([Info.ABILITY, Role(player.role), town.date, player.player_number, info])
                #         bool_print(player.info)

    
    for player in town.players:
        player.single_night_conditions = []
    
    bool_print('\033[1m Night '+ str(town.date) + ' \033[0m')
    print_town(town)
    check_end(town)

def kill_player(town, player, source):
    if player.alive:
        life = total_alive(town)
        player.alive = ('no_demon' in player.single_night_conditions if source == 'demon' else False)
        if not player.alive:
            if player.role == Role.SAINT and source == 'execute':
                give_win(town, 'Evil' if player.alignment == 'Good' else 'Good')
            # for p in town.players:
            #     p.wv.world[player.player_number].alive = False
            #     p.wv.world[player.player_number].death_source = ('night' if source == 'demon' else 'day') # Bad, change code
            player.death_source = source
            player.death_order_num = town.current_death_order_number
            town.current_death_order_number += 1
            player.just_died = True
            for p in town.players:
                p.wv.info.put([Info.DEATH, player.player_number])
        
            # Scarlet Woman
            if life >= 5 and check_for_alive_demon(town) == None and player.type == 'd':
                if  (check := check_for_role(town, Role.SCARLET_WOMAN)) != None:
                    check.type = player.type
                    check.role = player.role
                    #evil_share_roles(town)
                    # check.wv.world[check.player_number].myself = player.role
    check_end(town)

#find possible permutations of characters
#assign to existing players
#remove logically impossible permutations
# start_time = time.time()
# print("--- %s seconds ---" % (time.time() - start_time))
# @timethis
def worldview_solver(town, wv, demon=False): # Set demon=False # Function is only taking 0.37 sec normally, but ranges up to 0.6 in parallel
    # TODO: factor in deaths, poison, changes between days
    # Each perm is a list of strings
    while not wv.info.empty():
        facts = wv.info.get()
        bools = np.ones(len(wv.saved_permutations), dtype=bool)
        match facts[0]:
            case Info.MYSELF:
                bools = myself_condition(wv.saved_permutations, facts[1], facts[2])
            case Info.CLAIM:
                bools = claimed_condition(wv.saved_permutations, facts[1], facts[2])
            case Info.ABILITY:
                for i in range(len(wv.saved_permutations)):
                    perm = wv.saved_permutations[i]
                    bools[i] = not (perm[facts[3]] == facts[1] and not role_dict[facts[1]][2](perm, facts[-1]))
            case Info.DEATH:
                for i in range(len(wv.saved_permutations)):
                    perm = wv.saved_permutations[i]
                    curr_demon = alive_demon_in_perm(town, perm) # [Bool, player_num]
                    if not curr_demon[0]:
                        if town.players[curr_demon[1]].death_source == 'execute' and (sw := role_in_perm(town, perm, Role.SCARLET_WOMAN, True)) != None:
                            perm[sw] = Role.IMP
                        else:
                            curr_minion = alive_minion_in_perm(town, perm) # [Bool, player_num]
                            if town.players[curr_demon[1]].death_source == 'demon' and curr_minion[0]: # TODO: Need to check more than one minion
                                perm[curr_minion[1]] = Role.IMP
                            else:
                                bools[i] = False
        # TODO: Add in info about an attempted kill that fails?
        wv.saved_permutations = wv.saved_permutations[bools]

    bool_print('Possible worlds: ' + str(len(wv.saved_permutations)))
    wv.analysis = analyze_possibilities(town, wv.saved_permutations)
    #bool_print('Analysis: ' + str(wv.analysis))
    wv.evil_analysis = analyze_evil(town, wv.analysis, demon) # Change code
    bool_print('Evil: ' + str(wv.evil_analysis))

# Confirmed has to be that role -> all_permutations[:, 0] == 1
# Myself has to be that role, but could be drunk -> (all_permutations[:, 0] == 1) | (all_permutations[:, 0] == 17) (only for townsfolk/ < 14)
# Claimed has to be that role, or another role that could lie -> (all_permutations[:, 0]) == 1 | (all_permutations[:, 0] >= 18)
def confirmed_condition(arr, pos, role):
    return arr[:, pos] == role

def myself_condition(arr, pos, role):
    if role < 14:
        return (arr[:, pos] == role) | (arr[:, pos] == 17)
    return arr[:, pos] == role

def claimed_condition(arr, pos, role):
    if role < 14:
        return (arr[:, pos] == role) | (arr[:, pos] >= 17)
    return (arr[:, pos] == role) | (arr[:, pos] >= 18)

def analyze_possibilities(town, possibilities):
    possibilities_t = np.transpose(possibilities)
    output = np.zeros((7, 23), dtype=int)
    for i in range(town.size):
        output[i] = np.bincount(possibilities_t[i], minlength=23)
    return output

def analyze_evil(town, analysis, demon=False):
    output = np.zeros(town.size) # Could probably condense with numpy
    for i in range(town.size):
        #print(chance_of_evil(analysis[i]))
        output[i] = (chance_of_demon(analysis[i]) if demon else chance_of_evil(analysis[i]))
    return np.trunc(output * 100) / 100

def chance_of_evil(player_bincount):
    total_all = np.sum(player_bincount)
    total_evil = np.sum(player_bincount[18:])
    return total_evil/total_all

def chance_of_demon(player_bincount):
    total_all = np.sum(player_bincount)
    total_demon = player_bincount[22]
    return total_demon/total_all

def perform_first_info(town):
    for player in town.players:
        while not player.want_chat.empty():
            chat = player.want_chat.get()
            private_chat(player, chat[0], chat[1], chat[2])
    for player in town.players:
        public_claim_role(town, player.player_number, player.claim)
    for player in town.players:
        for piece in player.info:
            public_claim_info(town, player.player_number, piece)
        player.info = []
    #evil_share_roles(town)

def perform_later_info(town):
    for player in town.players:
        for piece in player.info:
            public_claim_info(town, player.player_number, piece)
        player.info = []

def public_claim_role(town, num, role):
    for player in town.players:
        player.wv.info.put([Info.CLAIM, num, role])

def public_claim_info(town, num, info):
    for player in town.players:
        player.wv.info.put(info)

def evil_share_roles(town):
    for player in town.players:
        if evil_type(player.type):
            for player2 in town.players:
                if evil_type(player2.type):
                    player.wv.info.put([Info.MYSELF, player2.player_number, player2.role])

def private_chat(origin_player, known_role, target_player, reason):
    match reason:
        case PrivateChat.WASH:
            if target_player.claim == known_role: # TODO: Evil should know what they're claiming? Need to consider guessing (10% chance twice)
                # tell 'yes'
            else:
                # tell 'no'
        case PrivateChat.LIBR:
            if target_player.claim == known_role: # Evil should know what they're claiming?
                # tell 'yes'
            else:
                # tell 'no'
        case PrivateChat.EVIL:
            target_player.wv.info.put([Info.MYSELF, origin_player.player_number, origin_player.role])

class Town:
    def __init__(self, size, script, all_permutations):
        self.size = size
        self.script = script

        self.players = []
        self.date = 1
        self.current_death_order_number = 1
        self.end = False
        self.out_of_play_roles = []
        self.bluffs = []
        self.drunk = []
        self.previous_day_execution = None
        self.final_day = False
        self.victory = 0

        self.all_permutations = all_permutations

class Player:
    def __init__(self, town, role, type, alignment, num):
        self.role = role
        self.type = type
        self.alignment = alignment
        self.player_number = num
        
        self.alive = True
        self.death_source = None
        self.death_order_num = None # First to die is 1, second is 2, etc
        self.death_vote = True
        self.just_died = False
        
        self.once_per_game = True
        self.single_night_conditions = []
        self.single_day_conditions = []
        self.info = []
        self.want_chat = queue.Queue() # Format is [target_player, known_role, reason]

        self.claim = role

        if role == Role.DRUNK:
            self.claim = town.drunk
        self.wv = worldview(town, self.claim, num)
        
        # if alignment == 'Evil' and evil_type(type):
        #     if town.bluffs: #check if not empty
        #         self.claim = town.bluffs.pop()
        
    def printout(self):
        return ('Alive' if self.alive else 'Dead') + f' {self.alignment} {self.role}'
    def current(self):
        return f'{Role(self.role).name}' if self.alive else f'\033[38;5;244m {Role(self.role).name} \033[0m'

class worldview:
    def __init__(self, town, own_role, num):
        #self.world = []
        self.saved_permutations = town.all_permutations
        self.info = queue.Queue()
        self.analysis = []
        self.evil_analysis = []
        self.pos = num
        self.info.put([Info.MYSELF, num, own_role])

def run_game(size, curr_script):
    all_permutations = load_permutations()
    town = Town(size, curr_script, all_permutations)
    #print('Game ' + str(i+1), end=" ")
    start(town, all_permutations)
    good_player = choose_random_player(town, 1)
    # bool_print('The good player is: ' + str(good_player.role.name))
    # bool_print('The Drunk is: ' + str(town.drunk.name))
    # for i in range(town.size):
    #     bool_print(f"{good_player.wv.world[i].claimed.name:<15}{town.players[i].role.name:<15}")
    while not town.end:
        perform_day(town)
        if not town.end:
            perform_night(town)
    for player in town.players:
        bool_print(player.wv.saved_permutations)
    return town.victory

def run_games(batch_size, size, curr_script):
    output = []
    for i in range(batch_size):
        output.append(run_game(size, curr_script))
    return output
    # TODO: Game Report

def save_permutations(all_permutations, path='perm_storage.npy'):
    np.save(path, all_permutations)

def load_permutations(path='perm_storage.npy'):
    output = np.load(path, allow_pickle=True)
    return output

def new_permutations(num_of_players):
    all_permutations = find_all_permutations(distributions[num_of_players]) # Trying to decrease overhead per new process
    save_permutations(all_permutations)
    print(all_permutations.shape)
    print('All permutations: ' + str(len(all_permutations)))
    print(np.size(all_permutations))

def bool_print(message):
    if True:
        print(message)
    # global num_games
    # if num_games == 1:
    #     print(message)

@timethis
def main():
    num_of_players = 7
    if False:
        new_permutations(num_of_players)
    curr_script = Script(poss_town_roles, poss_out_roles, poss_minion_roles, poss_demon_roles, \
                         role_dict, distributions)
    num_games = 1 # 284 sec to rune 10000
    total_good_wins = 0
    
    if num_games > 10:
        workers = os.cpu_count()
        batch_size = math.ceil(num_games / workers) # could use workers flag
        num_games = batch_size * workers
        with concurrent.futures.ProcessPoolExecutor(max_workers=workers) as executor:
            these_futures = [executor.submit(run_games, batch_size, num_of_players, curr_script) for i in range(workers)]
            concurrent.futures.wait(these_futures)
        
        results = []
        for future in these_futures:
            results.extend(future.result())
        total_good_wins = sum(results)
        print(str(sum(results)) + ' out of ' + str(len(results)))
        #total_good_wins = sum([future.result() for future in these_futures if future.result() != None])

    else:
        for i in range(num_games):
            total_good_wins += run_game(num_of_players, curr_script)
    
    if num_games > 0:
        print('\n' + str(total_good_wins/num_games))


# TODO: Better lying for evil, better droison, nominations and voting, good watching voting patterns, add imp jump ability, more players?, imp kill fail info
# 8 more roles to be added, permutations additional info (including probability), some good stay silent, update choices/preferences for role functions

# TODO: Incrimination? Would be a big deal, but very hard to manage. Private chats, out of play info

# Private chat array, needs to hold the type of chat

# TODONE: good preference for execution, demon preference for kills, add imp jump to solver, undertaker bug, some lying


if __name__ == '__main__':
    main()

    # num_of_players = 7
    # if True:
    #     new_permutations(num_of_players)
    # a_p = load_permutations()

    # start_time = time.time()

    # # Combining conditions
    # combined_condition = []
    # combined_condition.append(claimed_condition(a_p, 1, 2))
    # combined_condition.append(claimed_condition(a_p, 2, 3))
    # combined_condition.append(claimed_condition(a_p, 3, 4))
    # combined_condition.append(claimed_condition(a_p, 4, 5))
    # combined_condition.append(claimed_condition(a_p, 5, 7))
    # combined_condition.append(claimed_condition(a_p, 6, 8))
    # # combined_condition = claimed_condition(a_p, 1, 2) & claimed_condition(a_p, 2, 3) & \
    # #     claimed_condition(a_p, 3, 4) & claimed_condition(a_p, 4, 5) & claimed_condition(a_p, 5, 7) & claimed_condition(a_p, 6, 8) # Using AND
    # # combined_condition = condition1 | condition2  # Using OR

    # finished_bool = myself_condition(a_p, 0, 1)
    # for condition in combined_condition:
    #     finished_bool = finished_bool & condition

    # # Filtering using the combined condition
    # filtered_arr = a_p[finished_bool]
    # print(filtered_arr.shape)
    # #print(filtered_arr)
    # print("--- %s seconds ---" % (time.time() - start_time))
    # arr = np.random.rand(500000, 7)

    # start_time = time.time()
    
    # condition1 = arr[:, 0] > 0.5  # Condition on the first channel
    # condition2 = arr[:, 1] < 0.5  # Condition on the second channel
    # combined_condition = condition1 & condition2  # Using AND
    # filtered_arr = arr[combined_condition]
    # print(filtered_arr.shape)
    # print("--- %s seconds ---" % (time.time() - start_time))




    
    #raw_arr = RawArray('i', all_permutations.flatten())
    # all_permutations = np.copy(all_permutations)
    # raw_arr = np.array(raw_arr)
    # raw_arr = np.reshape(raw_arr, shape = [564480, 7])
    #share_permutations = np.frombuffer(raw_arr, dtype=np.dtype(raw_arr))

    

        # with concurrent.futures.ProcessPoolExecutor(max_workers=None) as executor:
        #     #worldview_solver(player.wv, True)
        #     s_time = time.time()
        #     # these_futures = executor.map(worldview_solver, town)
        #     # these_futures = [executor.submit(worldview_solver, player) for player in town]
        #     these_futures = [executor.submit(test, i) for i in range(7)]
        #     concurrent.futures.wait(these_futures)
        #     print(these_futures)
        #     print("--- Total Concurrent: %s seconds ---" % (time.time() - s_time))

        #worldview_solver(town, town[0].wv)
    # for perm in good_player.wv.saved_permutations:
    #     print(perm)