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
(trackLenght > 0 and trackLenght =< 50)}

abstract sig Data{}

sig BPM extends Data{
value: one Int
thrMax: one Int
thrMin: one Int
}

sig BloodPressure extends Data{
value: one Int
thrMax: one Int
thrMin: one Int
}

sig Steps extends Data{}

sig Temperature extends Data{}

sig Glucose extends Data{
value: one Int
thrMax: one Int
thrMin: one Int
}

sig IdentifyingData extends Data{}

sig GenericUser{
dataCollected: one UserData,
personalData: one IdentifyingData,
surveysAllowed: set SpecificIndividualsDataSurvey,
notifications: set Notifications
}

sig UsersData{
bpmUser: one BPM,
bloodPressureUser: one BloodPressure,
stepsUser: one Steps,
temperatureUser: one Temperature,
glucoseUser: one Glucose,
locationUser: one Position,
}

abstract sig Survey{
surveyID: one Int,
involvedThirdParty: one ThirdParty,
researchResult: one Int
}
{researchResult > 0}

sig AnonymizedDataSurvey extends Survey{
genericData: set UserData
}
{researchResult > 3}

sig SpecificIndividualsDataSurvey extends Survey{
specificData: set GenericUser
}
{researchResult =< 3}

abstract sig Notification{}

sig SignedOutFromSurvey extends Notification{
userInvolved: one User
}

sig SignedInASurvey extends Notification{
surveyInvolved: one Survey
}

sig Warning extends Notification{}

sig CallAmbulanceWarning extends Warning{
userWhoNeedsHelp: one User
warningID: one WarningID
}

sig WarningID{}

sig ThirdParty{
anonymSurveysCarriedOut: set AnonymizedDataSurvey,
specificSurveyCarriedOut: set SpecificIndividualsDataSurvey,
notifications: set Notification
}

sig EmergencyDispatcher{
warnings: set Warning,
}

--TODO TRACK4RUN
-------------------------------------------------------------------

fact SurveysIdAreUnique{
no disj ss1, ss2: SpecificIndividualsDataSurvey|no disj as1, as2: AnonymizedDataSurvey|
	(ss1.surveyID = ss2.surveyID and   as1.surveyID = as2.surveyID and  ss1.surveyID = as1.surveyID and
	 ss1.surveyID = as2.surveyID and  ss2.surveyID = as2.surveyID and  as1.surveyID = ss2.surveyID)
}

fact NotificationSentToUserCausedBySurvey{
all user: GenericUser, specificSurvey:  SpecificIndividualsDataSurvey|
 	(user in specificSurvey implies
		 (one sn1:  SignedInASurvey| sn1 in user.notifications and sn1.survey.surveyID = specificSurvey.surveyID)) and
	(user not in specificSurvey implies
		(no sn2: SignedInASurvey| sn2 in user.notifications and sn2.survey.surveyID = specificSurvey.surveyID))
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
		(user.dataCollectedglucoseUser.value < user.dataCollected.glucoseUser.thrMin or user.dataCollected.glucoseUser.value > user.dataCollected.glucoseUser.thrMax)	) iff
	(one ed: EmergencyDispatcher, aw: CallAmbulanceWarning| aw in ed.warnings and user in aw.userWhoNeedsHelp)
}

