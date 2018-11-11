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
(trackLenght > 0 and trackLenght =< 7)}

abstract sig Data{}

sig BPM extends Data{
value: one Int,
thrMax: one Int,
thrMin: one Int
}
{(value > 0 and value < 7) and (thrMax > 0 and thrMax < 7) and (thrMax > 0 and thrMax < 7)}

sig BloodPressure extends Data{
value: one Int,
thrMax: one Int,
thrMin: one Int
}
{(value > 0 and value < 7) and (thrMax > 0 and thrMax < 7) and (thrMax > 0 and thrMax < 7)}

sig Steps extends Data{}

sig Temperature extends Data{}

sig Glucose extends Data{
value: one Int,
thrMax: one Int,
thrMin: one Int
}
{(value > 0 and value < 7) and (thrMax > 0 and thrMax < 7) and (thrMax > 0 and thrMax < 7)}

sig IdentifyingData extends Data{}

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
locationUser: one Position,
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
{researchResult > 3 and #genericData = researchResult}

sig SpecificIndividualsDataSurvey extends Survey{
specificData: set GenericUser
}
{researchResult =< 3 and #specificData = researchResult}

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
warnings: set Warning,
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

--------------------------------------------------------------------

fact SurveysIdAreUnique{
no disj ss1, ss2: SpecificIndividualsDataSurvey|no disj as1, as2: AnonymizedDataSurvey|
	(ss1.surveyID = ss2.surveyID and   as1.surveyID = as2.surveyID and  ss1.surveyID = as1.surveyID and
	 ss1.surveyID = as2.surveyID and  ss2.surveyID = as2.surveyID and  as1.surveyID = ss2.surveyID)
}

fact WarningIDAreUnique{
no disj  caw1, caw2: CallAmbulanceWarning| caw1.warningID = caw2.warningID
}

fact IdentifyingDataAreUnique{
no disj usr1, usr2: GenericUser| usr1.personalData = usr2.personalData
}

fact NotificationSentToUserCausedBySurvey{
all user: GenericUser, specificSurvey:  SpecificIndividualsDataSurvey|
 	(user in specificSurvey.specificData implies
		 (one sn1:  SignedInASurvey| sn1 in user.notifications and sn1.surveyInvolved.surveyID = specificSurvey.surveyID)) and
	(user not in specificSurvey.specificData implies
		(no sn2: SignedInASurvey| sn2 in user.notifications and sn2.surveyInvolved.surveyID = specificSurvey.surveyID))
}

--TODO SIGNED OUT FUNCTION

fact NoAccessToDataWithoutUsersConsent{
all thp: ThirdParty, user: GenericUser, survey: SpecificIndividualsDataSurvey| 
	(survey in user.surveysAllowed and thp in survey.involvedThirdParty) iff
	survey in thp.specificSurveyCarriedOut
}

fact EmergencyDispathcerGetCallAmbulanceWarning{
all user: GenericUser| 
	(	(user.dataCollected.bpmUser.value < user.dataCollected.bpmUser.thrMin or user.dataCollected.bpmUser.value > user.dataCollected.bpmUser.thrMax) or
		(user.dataCollected.bloodPressureUser.value < user.dataCollected.bloodPressureUser.thrMin or user.dataCollected.bloodPressureUser.value > user.dataCollected.bloodPressureUser.thrMax) or
		(user.dataCollected.glucoseUser.value < user.dataCollected.glucoseUser.thrMin or user.dataCollected.glucoseUser.value > user.dataCollected.glucoseUser.thrMax)	) iff
	(one ed: EmergencyDispatcher, aw: CallAmbulanceWarning| aw in ed.warnings and user in aw.userWhoNeedsHelp)
}

fact DisqualifiedUsersAreNotActive{
(all opr: OpenRun| all ath1: Athlete| ath1 in opr.activeAth and (isTrue[ath1.attendant] and not isTrue[ath1.disqualified]))
 and (all  bir: ByInvitationRun|  all ath2: Athlete| ath2 in bir.activeAth and (isTrue[ath2.attendant] and not isTrue[ath2.disqualified]))
}

fact AthletesAreUnique{
(all opr: OpenRun| no disj ath1, ath2: Athlete| ath1.userAthlete.personalData = ath2.userAthlete.personalData and (ath1 in opr.subscribedAth and ath2 in opr.subscribedAth)) and
	(all bir: ByInvitationRun|  no disj ath1, ath2: Athlete| ath1.userAthlete.personalData = ath2.userAthlete.personalData and (ath1 in bir.subscribedAth and ath2 in bir.subscribedAth))
}

----------------------------------------------------------------------------------------------------------------------------------------------

pred showData4Help{
(all u: GenericUser| #u.surveysAllowed > 0 and #u.surveysAllowed = #u.notifications and #u.runsScheduled = 0) and
(all thp: ThirdParty| #thp.anonymSurveysCarriedOut > 0 and # thp.specificSurveyCarriedOut > 0) and
(all bpm: BPM| bpm.value = 3 and bpm.thrMax = 6 and bpm.thrMin = 1) and
(all bp: BloodPressure| bp.value = 3 and bp.thrMax = 6 and bp.thrMin = 1) and
(all gl: Glucose| gl.value = 3 and gl.thrMax = 6 and gl.thrMin = 1) 
}

run showData4Help for 3 but 3 GenericUser, 1 ThirdParty, 1  AnonymizedDataSurvey, 2 SpecificIndividualsDataSurvey, 1 EmergencyDispatcher
