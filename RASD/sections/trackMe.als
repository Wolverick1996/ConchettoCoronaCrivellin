open util/integer
open util/boolean

sig Position{
coordX: one Int,
coordY: one Int, 
}
{ coordX >= -3 and coordX =< 3 and coordY >= -6 and coordY =< 6 }

sig Track{
startPoint: one Position,
endPoint: one Position,
trackLenght: one Int,
stages: set Position
}
{((startPoint.coordX = endPoint.coordX and startPoint.coordY = endPoint.coordY) implies #stages > 0) and
	(trackLenght > 0 and trackLenght =< 7) and (#stages =< 7) and
	(#stages > 0 implies (startPoint not in stages and endPoint not in stages))}

abstract sig Data{}

sig BPM extends Data{
value: one Int,
thrMax: one Int,
thrMin: one Int
}
{(value > 0 and value < 7) and (thrMax > 0 and thrMax < 7) and
	(thrMin > 0 and thrMin < 7) and  thrMin < thrMax}

sig BloodPressure extends Data{
value: one Int,
thrMax: one Int,
thrMin: one Int
}
{(value > 0 and value < 7) and (thrMax > 0 and thrMax < 7) and
	(thrMin > 0 and thrMin < 7) and thrMin < thrMax}

sig Steps extends Data{}

sig Temperature extends Data{}

sig Glucose extends Data{
value: one Int,
thrMax: one Int,
thrMin: one Int
}
{(value > 0 and value < 7) and (thrMax > 0 and thrMax < 7) and
	(thrMin > 0 and thrMin < 7) and thrMin < thrMax}

sig IdentifyingData {}

sig GenericUser{
dataCollected: one UsersData,
personalData: one IdentifyingData,
surveysAllowed: set SpecificIndividualsDataSurvey,
notifications: set Notification,
runsScheduled: set Run
}

sig UsersData{
bpmUser: one BPM,
bloodPressureUser: one BloodPressure,
stepsUser: one Steps,
temperatureUser: one Temperature,
glucoseUser: one Glucose,
locationUser: one Position
}

sig Athlete{
userAthlete: one GenericUser,
disqualified: one Bool,
attendant: one Bool
}

sig SurveyID{}

abstract sig Survey{
surveyID: one SurveyID,
involvedThirdParty: one ThirdParty,
researchResult: one Int
}
{researchResult > 0 and researchResult < 7}

sig AnonymizedDataSurvey extends Survey{
genericData: set UsersData
}
{researchResult > 2 and #genericData = researchResult}

sig SpecificIndividualsDataSurvey extends Survey{
specificData: set GenericUser
}
{researchResult =< 2 and #specificData = researchResult}

abstract sig Notification{}

sig SignedInASurvey extends Notification{
surveyInvolved: one Survey
}

sig Warning extends Notification{}

sig CallAmbulanceWarning extends Warning{
userWhoNeedsHelp: one GenericUser,
warningID: one WarningID
}

sig WarningID{}

sig ThirdParty{
anonymSurveysCarriedOut: set AnonymizedDataSurvey,
specificSurveyCarriedOut: set SpecificIndividualsDataSurvey
}

sig EmergencyDispatcher{
warnings: set CallAmbulanceWarning,
}

abstract sig Run{
track: one Track,
organizer: some GenericUser,
spectators: set GenericUser,
activeAth: set Athlete,
subscribedAth: set Athlete
}

sig ByInvitationRun extends Run{
invitatedAthletes: set Athlete
}

sig OpenRun extends Run{}

--------------------------------------------------------------------------------------------

fact SurveysIdAreUnique{all s1, s2: Survey|	
	s1.surveyID = s2.surveyID implies s1 = s2}

fact WarningIDAreUnique{all caw1, caw2: CallAmbulanceWarning|
	caw1.warningID = caw2.warningID implies caw1 = caw2}

fact IdentifyingDataAreUnique{all usr1, usr2: GenericUser|	
	usr1.personalData = usr2.personalData implies usr1 = usr2}

fact NotificationSentToUserCausedBySurvey{
all user: GenericUser, specificSurvey:  SpecificIndividualsDataSurvey|
 	(user in specificSurvey.specificData implies
		 (one sn1:  SignedInASurvey| sn1 in user.notifications and sn1.surveyInvolved.surveyID = specificSurvey.surveyID)) and
	(user not in specificSurvey.specificData implies
		(no sn2: SignedInASurvey| sn2 in user.notifications and sn2.surveyInvolved.surveyID = specificSurvey.surveyID))
}

fact EmergencyDispathcerGetCallAmbulanceWarning{
all user: GenericUser| 
	(	(user.dataCollected.bpmUser.value < user.dataCollected.bpmUser.thrMin or user.dataCollected.bpmUser.value > user.dataCollected.bpmUser.thrMax) or
		(user.dataCollected.bloodPressureUser.value < user.dataCollected.bloodPressureUser.thrMin or user.dataCollected.bloodPressureUser.value > user.dataCollected.bloodPressureUser.thrMax) or
		(user.dataCollected.glucoseUser.value < user.dataCollected.glucoseUser.thrMin or user.dataCollected.glucoseUser.value > user.dataCollected.glucoseUser.thrMax)
	) iff
	(one ed: EmergencyDispatcher, aw: CallAmbulanceWarning| aw in ed.warnings and user in aw.userWhoNeedsHelp)
}

fact DisqualifiedUsersAreNotActive{
(all opr: OpenRun| all ath1: Athlete| ath1 in opr.activeAth and (isTrue[ath1.attendant] and not isTrue[ath1.disqualified]))
 and (all  bir: ByInvitationRun|  all ath2: Athlete| ath2 in bir.activeAth and (isTrue[ath2.attendant] and not isTrue[ath2.disqualified]))
}

fact AthletesAreUnique{
(all opr: OpenRun| no disj ath1, ath2: Athlete|
	ath1.userAthlete.personalData = ath2.userAthlete.personalData and (ath1 in opr.subscribedAth and ath2 in opr.subscribedAth)) and
(all bir: ByInvitationRun|  no disj ath1, ath2: Athlete|
	ath1.userAthlete.personalData = ath2.userAthlete.personalData and (ath1 in bir.subscribedAth and ath2 in bir.subscribedAth))
}

fact NoNotificForAnonSurvey{all n: SignedInASurvey| some sp: SpecificIndividualsDataSurvey|
	 sp in n.surveyInvolved}

fact UsersDataExistWithUsers{all d: UsersData| some u: GenericUser|
	d in u.dataCollected}

fact TrackExistOnlyInRuns{all t: Track| some r: Run|
	t in r.track}

fact IdentifDataExistWithUsers{all id: IdentifyingData| some u: GenericUser|
	id in u.personalData}

fact SurveyIdExistWIthSurvey{all sid: SurveyID| some s: Survey|
	sid in s.surveyID}

fact NotificExistWithUsers{all n: SignedInASurvey| some u: GenericUser|
	n in u.notifications}

fact WarningIdExistWithWarning{all wid: WarningID| some caw: CallAmbulanceWarning|
	wid in caw.warningID}

fact PositionExistInSthElse{all p: Position| some t: Track, ud: UsersData|
	(p in t.startPoint or p in t.endPoint or p in t.stages) or (p in ud.locationUser)}

fact BPMExistInSthElse{all bpm: BPM| some ud: UsersData|
	bpm in ud.bpmUser}

fact BloodPressExistInSthElse{all blp: BloodPressure| some ud: UsersData|
	blp in ud.bloodPressureUser}


fact GlucoseExistInSthElse{all g: Glucose| some ud: UsersData|
	g in ud.glucoseUser}
--------------------------------------------------------------------------------------------

pred show{
all u: GenericUser| some t: ThirdParty| some sp: SpecificIndividualsDataSurvey|
	 (sp.specificData = u and sp.involvedThirdParty = t)
#GenericUser = 3
#AnonymizedDataSurvey = 1
}

--------------------------------------------------------------------------------------------

run show for 5 but 1 Run, 1 EmergencyDispatcher, 1 CallAmbulanceWarning, 1 
